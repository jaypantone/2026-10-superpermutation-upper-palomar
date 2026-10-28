# Superpermutation Almanac submission: upper

This branch is one standalone submission for the upper repository. Submit the
companion repository separately. The source snapshot follows the live
[Lean directions](https://web-production-daed9.up.railway.app/lean) and
[agent directions](https://web-production-daed9.up.railway.app/lean.txt)
read on October 28, 2026. It replaces the old single-`almanac_claim` interface.
The original Palomar metadata, independent Challenges and historical receipts
remain available for their original purpose; they do not configure this batch.

## Selected results

Write F₃(n) = n! + (n−1)! + (n−2)!.

| Entry theorem | Kind | Statement |
|---|---|---|
| `asymptotic_upper` | `Almanac.AsymptoticUpper (926683/1814400)` | Eventually, S(n) ≤ F₃(n) + (926683/1814400 + ε)(n−3)! for every positive rational ε. |

The public bounds page on October 28, 2026 showed the kernel-checked upper
coefficient 1771/3456; 926683/1814400 is smaller. The hosted preview must
recheck eligibility against the records at submission time.

The parameterized finite construction theorem and its numerical existence
corollaries remain in `Solution.lean`; they are supporting results, not batch
entries. Finite upper records require actual checked words through the separate
word-submission workflow. The four word artifacts under `words/` are preserved
but are not submitted by this Lean batch.

## Files and papers

`AlmanacSolution.lean` contains only imports, the `AlmanacSubmission` namespace,
and one theorem per result proved by a named imported theorem. Linking proofs
are in `AlmanacAdapter.lean`; `AlmanacAxioms.lean` reports every entry's axioms.
The four reserved libraries are declared at the root in `lakefile.toml`.

Lean is pinned to `leanprover/lean4:v4.35.0`, with Mathlib at
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The three judge-owned files are exact
copies of the site's batch scaffold, version 2. Neither placeholder is imported
by the proof. The judge replaces them with its own files.

The site archives `paper/`, not `papers/`. `paper/` contains byte-identical
copies of the existing papers and their sources. After editing/rebuilding
`papers/`, refresh these copies before submitting. The preflight verifies that
they agree and that the site selects every file. The copies do not alter the
mathematical content or extend the submitted theorem scope.

## Reproduce the preparation checks

On this Mac, use the existing shared compiler and expanded Mathlib cache,
with outputs outside Dropbox:

```sh
python3 -B tools/check.py AlmanacAxioms --receipt almanac-batch-20261028.json
```

In an external checkout with the pinned toolchain and dependencies, the site's
build command is `lake build AlmanacSolution`; `lake build AlmanacAxioms`
additionally prints the assumptions. Ordinary Lake does not inherit this
repository's local compiler/memory/disk guard; see [BUILD.md](BUILD.md).

Download and unpack the current
[judge source](https://web-production-daed9.up.railway.app/lean/judge-source.tar.gz)
outside Dropbox. From that directory:

```sh
python3 -B -m lean.batch.validate /absolute/path/to/this/repository
```

Then run this repository's fuller static preflight:

```sh
python3 -B scripts/check-almanac.py \
  --judge-source /absolute/path/to/unpacked-judge \
  --mathlib-manifest /absolute/path/to/pinned/mathlib/lake-manifest.json \
  --receipt verification/almanac/preflight.json
```

It checks the official batch grammar, root layout, exact judge files, pinned
manifest, repository/source restrictions, and paper selection. The source scan
can report `sorry` in the retained independent Palomar Challenges and custom
macros in supporting proofs. Those are not proof axioms: the solution does not
import a Challenge, and this batch uses only standard-axiom proofs, not
`native_decide`. The axiom audit must report only `propext`, `Classical.choice`,
and `Quot.sound` for each submitted theorem.

`verification/almanac/` records download hashes, static checks, the local build
and axiom output. A local build and these source checks are not a fresh Lean
export replay, NanoDa replay, hosted preview, acceptance, or publication. The
site performs its own build, comparison, axiom checks and both kernel replays.

## Submit this repository

1. Push branch `almanac/batch-2026-10-28` to
   `https://github.com/jaypantone/2026-10-superpermutation-upper-palomar`.
2. Sign in at the [Lean submission form](https://web-production-daed9.up.railway.app/lean/submit).
   Select that repository and the branch, or paste the full commit hash.
3. Read the generated preview, including each statement, current eligibility,
   authors and paper files. Credit Jay Pantone (`jaypantone`); inherited work's
   attribution is retained in the repository notices.
4. Give the source-hosting permission in the form and submit. The judge uses
   the previewed immutable commit even if the branch later moves.
5. Keep the branch until My submissions says Archived. Submit the companion
   repository as a separate batch; an account may have only one batch being
   checked at a time.

This preparation makes no submission and does not push the branch. Both
repositories' `main` references remain unchanged.
