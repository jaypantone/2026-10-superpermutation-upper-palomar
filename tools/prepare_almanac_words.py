"""Canonicalize the four archived words, encode Detour, and run the public checkers.

Build detour, classcheck, wordhash and bitmapcheck from the site's downloadable
sources first, outside Dropbox. This streams the large words without expanding
them on disk and never uploads anything. Original word files are not modified.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import lzma
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    with path.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tools-dir", type=Path, required=True)
    parser.add_argument("--degrees", type=int, nargs="+", default=[10, 11, 12, 13])
    args = parser.parse_args()
    binaries = {n: args.tools_dir.resolve() / n
                for n in ["detour", "classcheck", "wordhash", "bitmapcheck"]}
    for binary in binaries.values():
        if not binary.is_file():
            raise RuntimeError(f"Missing public tool: {binary}")
    output = ROOT / "words/almanac"
    output.mkdir(exist_ok=True)
    records = ROOT / "verification/almanac/words"
    records.mkdir(parents=True, exist_ok=True)
    for word in json.loads((ROOT / "words/manifest.json").read_text())["words"]:
        n, length = word["symbols"], word["length"]
        if n not in args.degrees:
            continue
        source = ROOT / word["path"]
        if digest(source) != word["sha256"]:
            raise RuntimeError(f"Archived word {n} changed")
        destination = output / f"superpermutation-{n}-{length}.detour"
        temporary = destination.with_suffix(".detour.partial")
        started = time.monotonic()
        raw_hash, canonical_hash, count = hashlib.sha256(), hashlib.sha256(), 0
        alphabet = word["alphabet"].encode("ascii")
        with (lzma.open(source, "rb") if word["format"] == "xz" else source.open("rb")) as stream:
            prefix = stream.read(n)
            if sorted(prefix) != sorted(alphabet):
                raise RuntimeError(f"Word {n} does not start with a permutation")
            table = bytes.maketrans(prefix, alphabet)
            log = records / f"{n}-encode.log"
            with log.open("w") as stderr:
                proc = subprocess.Popen([str(binaries["detour"]), "encode", "--n", str(n),
                                         "-", str(temporary)], stdin=subprocess.PIPE,
                                        stdout=stderr, stderr=stderr)
                try:
                    chunk = prefix
                    while chunk:
                        raw_hash.update(chunk)
                        converted = chunk.translate(table)
                        canonical_hash.update(converted)
                        count += len(chunk)
                        proc.stdin.write(converted)
                        chunk = stream.read(1024 * 1024)
                    proc.stdin.close()
                    if proc.wait(timeout=900) != 0:
                        raise RuntimeError(f"Encoding failed; see {log}")
                finally:
                    if proc.poll() is None:
                        proc.kill()
                        proc.wait()
        if count != length or raw_hash.hexdigest() != word["raw_sha256"]:
            raise RuntimeError(f"Decoded source identity failed for {n}")
        info = subprocess.run([str(binaries["detour"]), "info", str(temporary)],
                              check=True, capture_output=True, text=True, timeout=900)
        decoded = json.loads(info.stdout)
        if decoded["length"] != length or decoded["sha256"] != canonical_hash.hexdigest():
            raise RuntimeError(f"Detour round-trip identity failed for {n}")
        if temporary.stat().st_size > 200 * 1024**2:
            raise RuntimeError("Upload exceeds 200 MiB")
        checks = {}
        for checker in ["classcheck", "wordhash", "bitmapcheck"]:
            result = subprocess.run([str(binaries[checker]), str(n), str(temporary), str(length)],
                                    capture_output=True, text=True, timeout=900, check=True)
            (records / f"{n}-{checker}.log").write_text(result.stdout + result.stderr)
            checks[checker] = json.loads(result.stdout)
            if checker in {"classcheck", "bitmapcheck"} and checks[checker].get("missing") != 0:
                raise RuntimeError(f"Missing permutations in {checker} for {n}")
        for key in ["length", "perm_windows", "distinct", "missing"]:
            if checks["classcheck"][key] != checks["bitmapcheck"][key]:
                raise RuntimeError(f"Coverage checkers disagree on {key} for {n}")
        if checks["classcheck"]["repeated_occurrences"] != checks["bitmapcheck"]["perm_windows"] - checks["bitmapcheck"]["distinct"]:
            raise RuntimeError(f"Repeated-occurrence counts disagree for {n}")
        if checks["wordhash"]["sha256"] != canonical_hash.hexdigest():
            raise RuntimeError(f"Public wordhash disagrees with canonical stream for {n}")
        temporary.replace(destination)
        record = {
            "status": "PASS", "recorded_utc": datetime.now(timezone.utc).isoformat(),
            "n": n, "length": length, "file": str(destination.relative_to(ROOT)),
            "bytes": destination.stat().st_size, "file_sha256": digest(destination),
            "source_file": word["path"], "source_raw_sha256": raw_hash.hexdigest(),
            "canonical_raw_sha256": canonical_hash.hexdigest(),
            "relabel_from": prefix.decode(), "relabel_to": alphabet.decode(),
            "round_trip": decoded, "checks": checks,
            "tools_sha256": {n: digest(p) for n, p in binaries.items()},
            "seconds": round(time.monotonic() - started, 3),
            "submitted": False,
        }
        (records / f"{n}.json").write_text(json.dumps(record, indent=2) + "\n")
        print(f"PASS n={n}: {length} letters, {record['bytes']} uploaded bytes, "
              f"SHA-256 {record['canonical_raw_sha256']}", flush=True)


if __name__ == "__main__":
    main()
