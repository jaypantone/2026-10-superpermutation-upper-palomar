# The four explicit superpermutations

These are the complete words underlying the finite upper bounds presented
here. Each symbol is one ASCII byte. The alphabet is the first n characters
of `0123456789ABC`; there is no final newline.

| n | Length | Format | Stored size | Distinct permutations checked |
|---:|---:|---|---:|---:|
| 10 | 4,034,857 | Plain text | 4.03 MB | 3,628,800 = 10! |
| 11 | 43,930,548 | Plain text | 43.93 MB | 39,916,800 = 11! |
| 12 | 522,737,007 | XZ | 3.57 MB | 479,001,600 = 12! |
| 13 | 6,747,802,736 | XZ | 38.89 MB | 6,227,020,800 = 13! |

Stored sizes use decimal megabytes. These are the words produced by this
development, not a list of current records. See the
[comparison with announced results](../docs/RELATED_WORK.md).

[manifest.json](manifest.json) records every file's packed and decoded
byte counts and SHA-256 hashes. [coverage.json](coverage.json) records literal scans performed on 9 October
2026 on the exact decoded bytes with the included streaming checker. The files
and this record are carried forward unchanged from the earlier release; this
repackaging does not claim a new coverage scan.
All four scans found every permutation. Repacking preserves the word bytes
exactly, verified by a full decompression and hash comparison.

## Verify the downloaded files

From the repository root:

```sh
python3 -B tools/verify_words.py
```

This streams the decoded words and compares both hashes and byte counts.
It uses bounded buffers and at most 300 MiB for the XZ decoder. It does not
write out the large words or repeat the permutation-coverage calculation.
Use `--degrees 10 11` to check only those files.

For an independent coverage check, compile the streaming C++ checker:

```sh
c++ -O3 -std=c++17 tools/check_coverage.cpp -o /tmp/superperm-check-coverage
/tmp/superperm-check-coverage --self-test
nice -n 10 /tmp/superperm-check-coverage 10 0123456789 \
  words/10/superpermutation-10-4034857.txt
```

The checker scans all length-n factors, ranks each permutation, and counts
the distinct ranks. It reads through the end of the input, rejects any byte
outside the alphabet (including a final newline), and exits successfully
only if all n! ranks occur. Its JSON output gives the length, number of valid
permutation occurrences, and numbers of distinct and missing permutations.
The self-test compares every word of length at most eight on alphabets of
size two and three with direct checks, and exhaustively checks permutation
ranking through degree nine.

For a compressed word, decode directly into the checker. Use `pipefail` so
that a decompression error also makes the command fail:

```sh
set -o pipefail
nice -n 10 xz --threads=1 --memlimit-decompress=300MiB -dc \
  words/13/superpermutation-13-6747802736.txt.xz | \
  nice -n 10 /tmp/superperm-check-coverage 13 0123456789ABC -
```

The checker stores one bit per permutation, approximately 743 MiB for
thirteen symbols, plus a 1 MiB input buffer. The command also limits XZ to one decoding worker
and 300 MiB of decoder memory. Neither program writes the decoded word to disk. Coverage
does not establish byte identity with the recorded file; run the hash
check above for that purpose. These ordinary program checks are separate
from the Lean proofs of the general construction.

## Compression

The twelve- and thirteen-symbol files use the earlier repository's XZ recipe:
a delta filter with distance n, then LZMA2 at preset 9 extreme with a 256 MiB
dictionary, `lc=4`, `lp=0`, `pb=0`, and an XZ SHA-256 integrity check.
The filter exploits the recurring distance-n structure of the words.

`tools/compress_word.py` reproduces this recipe. It accepts a plain or XZ
source, streams the input, and checks the complete decoded output against
the required raw SHA-256 before publishing the compressed file. For example:

```sh
nice -n 10 python3 -B tools/compress_word.py /tmp/superpermutation-12.txt \
  /tmp/superpermutation-12.txt.xz --degree 12 \
  --expected-sha256 2ddb9ff55274c5bbd4562b524303e3988faed29fd3f58513f134f954aef86c37
```

The default `--threads 1` uses the original Python encoder, about 3 GB of
memory, and one CPU core. Optional `--threads 2` or `--threads 3` uses the
installed `xz` program with the same filters and dictionary, compressing
independent 512 MiB blocks with at most that many workers. It sets a 16 GiB
XZ compression-memory limit and forbids automatic changes to the dictionary
or encoding mode. XZ may use fewer workers to meet the limit. A smaller
parallel block size can be selected with `--block-mib` (1 through 512).

The bundled twelve-symbol file uses serial encoding. The thirteen-symbol
file uses `--threads 3 --block-mib 512`; the manifest records these settings.

Serial and parallel encoding can produce different compressed bytes and
file sizes. Both branches verify the complete decoded hash before publishing
the output, and report their encoding settings. Decompression uses much less
memory. The files are lossless; the filter changes neither the alphabet nor
the word.

## Attribution

All four words use Pantone's construction, developed in the
[43/80 repository](https://github.com/jaypantone/superperm-upper-43-80).
The improvements here optimize the choices, ordering, or openings of its pieces.

- **10 symbols:** Pantone's pair-switched 350-trail selection, with the mixed
  trail organization following rumstd's pull request #3 to the earlier
  repository, and our subsequent arrangement and cut optimization.
- **11 symbols:** Halfar's selection X and starting plan, with our block
  images, arrangement, and openings.
- **12 symbols:** Halfar's selection E and starting word of length
  522,737,299, with our order and cuts.
- **13 symbols:** Halfar's selection N and generator, with our order and cuts.

Halfar's source is [jhalfar/superpermutations](https://github.com/jhalfar/superpermutations).
The upper-bound paper describes the mathematical construction; these credits
distinguish the inherited selections from the improvements made here.
