#!/usr/bin/env python3
"""Verify retained word bytes without extracting files or checking coverage.

Packed and decoded SHA-256/byte counts are compared with words/manifest.json.
A matching hash establishes identity with the recorded file; it does not prove
that every permutation occurs. No files are written by this program.
"""
from pathlib import Path
import argparse
import hashlib
import json
import lzma
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
CHUNK_BYTES = 1024 * 1024
DECODER_MEMORY_LIMIT = 300 * 1024 * 1024


class VerificationError(Exception):
    pass


def decoded_xz_chunks(chunks):
    """Decode concatenated XZ streams, accepting standard four-byte padding.

    Both input and returned output chunks are bounded. The decoder separately
    enforces a 300 MiB dictionary/workspace limit (the dictionary is 256 MiB).
    """
    decoder = lzma.LZMADecompressor(format=lzma.FORMAT_XZ, memlimit=DECODER_MEMORY_LIMIT)
    between_streams, padding, streams = False, 0, 0
    for packet in chunks:
        data = packet
        while True:
            if between_streams:
                rest = data.lstrip(b'\0')
                padding += len(data) - len(rest)
                data = rest
                if not data:
                    break
                if padding % 4:
                    raise VerificationError('XZ stream padding is not a multiple of four bytes')
                decoder = lzma.LZMADecompressor(format=lzma.FORMAT_XZ,
                                               memlimit=DECODER_MEMORY_LIMIT)
                between_streams, padding = False, 0
            output = decoder.decompress(data, max_length=CHUNK_BYTES)
            data = b''
            if output:
                yield output
            if decoder.eof:
                streams += 1
                between_streams = True
                data = decoder.unused_data
            elif decoder.needs_input:
                break
            # Otherwise drain bounded output using an empty input packet.
    if not between_streams or streams == 0:
        raise VerificationError('Incomplete or empty XZ stream')
    if padding % 4:
        raise VerificationError('Final XZ padding is not a multiple of four bytes')


def verify_entry(entry, root=ROOT):
    path = (root / entry['path']).resolve()
    if not path.is_relative_to(root.resolve()) or not path.is_file():
        raise VerificationError('Selected word path must identify an existing file inside this repository')
    if path.stat().st_size != entry['bytes']:
        raise VerificationError('Packed byte count differs from the manifest')
    packed_hash, raw_hash = hashlib.sha256(), hashlib.sha256()
    packed_bytes, raw_bytes = 0, 0
    with path.open('rb') as source:
        def packets():
            nonlocal packed_bytes
            while block := source.read(CHUNK_BYTES):
                packed_bytes += len(block)
                if packed_bytes > entry['bytes']:
                    raise VerificationError('Packed file grew beyond its recorded size')
                packed_hash.update(block)
                yield block
        chunks = packets()
        if entry['format'] == 'xz':
            chunks = decoded_xz_chunks(chunks)
        for block in chunks:
            raw_bytes += len(block)
            if raw_bytes > entry['raw_bytes']:
                raise VerificationError('Decoded word exceeds its recorded size')
            raw_hash.update(block)
    actual = {'bytes': packed_bytes, 'sha256': packed_hash.hexdigest(),
              'raw_bytes': raw_bytes, 'raw_sha256': raw_hash.hexdigest()}
    for field, value in actual.items():
        if value != entry[field]:
            raise VerificationError(f'{field} differs: recorded {entry[field]}, observed {value}')
    return actual


def read_manifest(path, root=ROOT):
    manifest = json.loads(path.read_text())
    if not isinstance(manifest, dict):
        raise VerificationError('Word manifest must be a JSON object')
    version = manifest.get('schema', manifest.get('schema_version'))
    if type(version) is not int or version != 1 or ('schema' in manifest and 'schema_version' in manifest
                        and manifest['schema'] != manifest['schema_version']):
        raise VerificationError('Expected word-manifest schema 1')
    entries = manifest.get('words')
    if not isinstance(entries, list) or not entries:
        raise VerificationError('Manifest has no words')
    seen_degrees, seen_paths = set(), set()
    for entry in entries:
        if not isinstance(entry, dict):
            raise VerificationError('Word entry must be an object')
        for field in ('symbols', 'length', 'bytes', 'raw_bytes'):
            if type(entry.get(field)) is not int or entry[field] < 1:
                raise VerificationError('Expected positive integer field: ' + field)
        for field in ('sha256', 'raw_sha256'):
            if not isinstance(entry.get(field), str) or not re.fullmatch('[0-9a-f]{64}', entry[field]):
                raise VerificationError('Expected lowercase SHA-256 field: ' + field)
        if entry.get('format') not in {'raw', 'xz'}:
            raise VerificationError('Expected format raw or xz')
        alphabet = entry.get('alphabet')
        if isinstance(alphabet, list):
            if not all(isinstance(c, str) and len(c) == 1 for c in alphabet):
                raise VerificationError('Alphabet list must contain single characters')
            alphabet = ''.join(alphabet)
        if (not isinstance(alphabet, str) or not alphabet.isascii()
                or len(alphabet) != entry['symbols'] or len(set(alphabet)) != len(alphabet)):
            raise VerificationError('Alphabet must contain the stated number of distinct ASCII symbols')
        if entry['length'] != entry['raw_bytes'] or entry.get('final_lf', False) is not False:
            raise VerificationError('Expected one byte per symbol, with no final newline')
        relative = entry.get('path')
        if (not isinstance(relative, str) or not relative or Path(relative).is_absolute()
                or '..' in Path(relative).parts):
            raise VerificationError('Expected a repository-relative word path without ..')
        path = (root / relative).resolve()
        if not path.is_relative_to(root.resolve()):
            raise VerificationError('Word path must stay inside this repository')
        if entry['symbols'] in seen_degrees or path in seen_paths:
            raise VerificationError('Duplicate word degree or file path')
        seen_degrees.add(entry['symbols'])
        seen_paths.add(path)
    return entries


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--degrees', nargs='+', type=int,
                        help='Verify only these alphabet sizes; default: all retained words')
    args = parser.parse_args()
    try:
        entries = read_manifest(ROOT/'words/manifest.json')
        if args.degrees:
            available = {entry['symbols'] for entry in entries}
            missing = set(args.degrees) - available
            if missing:
                raise VerificationError('Degrees absent from the manifest: ' + ', '.join(map(str, sorted(missing))))
            entries = [entry for entry in entries if entry['symbols'] in args.degrees]
        for entry in entries:
            print(f"Checking n={entry['symbols']}: {entry['path']}", flush=True)
            verify_entry(entry)
            print(f"PASS n={entry['symbols']}: packed and raw SHA-256 and byte counts match.", flush=True)
    except (VerificationError, OSError, ValueError, KeyError, TypeError, lzma.LZMAError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        return 1
    print(f'PASS: byte identity verified for {len(entries)} word(s); permutation coverage was not checked.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
