#!/usr/bin/env python3
"""Compress an ASCII word as XZ and check its complete decompressed hash."""

import argparse
from contextlib import suppress
import hashlib
import json
import lzma
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--degree", type=int, required=True)
    parser.add_argument("--expected-sha256", required=True,
                        help="SHA-256 of the decoded word bytes, preserving all whitespace; for an XZ source this is not the packed-file hash")
    parser.add_argument("--dictionary-mib", type=int, default=256)
    parser.add_argument("--threads", type=int, choices=(1, 2, 3), default=1,
                        help="Default 1 preserves the original Python encoder; 2 or 3 use block-parallel xz")
    parser.add_argument("--block-mib", type=int,
                        help="Block size for parallel xz only (1..512 MiB; default 512)")
    args = parser.parse_args()
    if not 2 <= args.degree <= 13 or not 1 <= args.dictionary_mib <= 256:
        parser.error("Degree must be 2..13 and dictionary size 1..256 MiB")
    if not re.fullmatch("[0-9a-f]{64}", args.expected_sha256):
        parser.error("Expected a lowercase, 64-character SHA-256 of the decoded word")
    if args.block_mib is not None and (args.threads == 1 or not 1 <= args.block_mib <= 512):
        parser.error("--block-mib requires --threads 2 or 3 and a value between 1 and 512")
    xz = shutil.which("xz") if args.threads > 1 else None
    if args.threads > 1 and xz is None:
        parser.error("Parallel encoding requires xz on PATH")
    block_mib = (args.block_mib or 512) if args.threads > 1 else None
    partial = args.output.with_suffix(args.output.suffix + ".partial")
    if args.output.exists() or partial.exists():
        parser.error("Output already exists")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    total = None if args.source.suffix == ".xz" else args.source.stat().st_size
    started = last_report = time.monotonic()
    filters = [
        {"id": lzma.FILTER_DELTA, "dist": args.degree},
        {"id": lzma.FILTER_LZMA2, "preset": 9 | lzma.PRESET_EXTREME,
         "dict_size": args.dictionary_mib << 20, "lc": 4, "lp": 0, "pb": 0},
    ]
    compressor = None
    if args.threads == 1:
        compressor = lzma.LZMACompressor(format=lzma.FORMAT_XZ,
                                       check=lzma.CHECK_SHA256, filters=filters)
    digest = hashlib.sha256()
    consumed = 0
    encoding = {"mode": "serial-python" if args.threads == 1 else "block-parallel-xz",
                "worker_limit": args.threads, "block_mib": block_mib,
                "dictionary_mib": args.dictionary_mib,
                "xz_memory_limit_gib": 16 if args.threads > 1 else None}
    print(json.dumps({"phase": "compressing", "degree": args.degree,
                      "input_bytes": total, "pid": os.getpid(),
                      "encoding": encoding}), flush=True)
    opener = lzma.open if args.source.suffix == ".xz" else open
    with opener(args.source, "rb") as source, partial.open("xb") as target:
        process = None
        try:
            if xz is not None:
                # Ignore user defaults that could change filters, threads, or limits.
                environment = dict(os.environ)
                environment.pop("XZ_DEFAULTS", None)
                environment.pop("XZ_OPT", None)
                command = [xz, "--compress", "--format=xz", f"--threads={args.threads}",
                           f"--block-size={block_mib}MiB", "--memlimit-compress=16GiB",
                           "--no-adjust", "--check=sha256", f"--delta=dist={args.degree}",
                           f"--lzma2=preset=9e,dict={args.dictionary_mib}MiB,lc=4,lp=0,pb=0", "-c"]
                process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=target,
                                           env=environment)
            for chunk in iter(lambda: source.read(4 << 20), b""):
                digest.update(chunk)
                if process is None:
                    target.write(compressor.compress(chunk))
                else:
                    process.stdin.write(chunk)
                consumed += len(chunk)
                now = time.monotonic()
                if now - last_report >= 30:
                    print(json.dumps({"phase": "compressing", "degree": args.degree,
                                      "input_bytes_consumed": consumed,
                                      "seconds": round(now - started, 1)}), flush=True)
                    last_report = now
            if process is None:
                target.write(compressor.flush())
            else:
                process.stdin.close()
                code = process.wait()
                if code:
                    raise RuntimeError(f"xz failed with exit status {code}")
        except BaseException:
            if process is not None:
                if process.poll() is None:
                    with suppress(ProcessLookupError):
                        process.terminate()
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    with suppress(ProcessLookupError):
                        process.kill()
                    process.wait()
                with suppress(OSError):
                    process.stdin.close()
            # Leave the unpublished .partial file available for diagnosis.
            raise
    del compressor
    if (total is not None and consumed != total) or digest.hexdigest() != args.expected_sha256:
        raise ValueError("Input differs from the verified word")
    total = consumed
    restored = hashlib.sha256()
    restored_size = 0
    with lzma.open(partial, "rb") as source:
        for chunk in iter(lambda: source.read(4 << 20), b""):
            restored.update(chunk)
            restored_size += len(chunk)
    if restored_size != total or restored.hexdigest() != args.expected_sha256:
        raise ValueError("Decompressed word differs from the verified input")
    packed_hash = hashlib.sha256()
    with partial.open("rb") as source:
        for chunk in iter(lambda: source.read(4 << 20), b""):
            packed_hash.update(chunk)
    if args.output.exists():
        raise FileExistsError(args.output)
    partial.rename(args.output)
    print(json.dumps({"phase": "complete", "degree": args.degree,
                      "input_bytes": total, "file_sha256": restored.hexdigest(),
                      "compressed_bytes": args.output.stat().st_size,
                      "compressed_sha256": packed_hash.hexdigest(),
                      "roundtrip_verified": True,
                      "encoding": encoding,
                      "seconds": round(time.monotonic() - started, 2)}), flush=True)


def terminate_run(signum, _frame):
    # Turn ordinary external cancellation into an exception so the parallel
    # branch terminates and reaps its xz child before this process exits.
    raise KeyboardInterrupt(f"Compression cancelled by signal {signum}")


if __name__ == "__main__":
    signal.signal(signal.SIGTERM, terminate_run)
    main()
