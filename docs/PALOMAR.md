# Palomar submission

This repository contains the statements, proofs, metadata, and pinned build
inputs for the configurations below. It has not yet been registered with
Palomar. The [official submission guide](https://palomar-registry.org/how-to-submit)
describes the current process; its requirements were reviewed on 24 October
2026.

## Entries

| Configuration | Claims |
|---|---|
| `comparator.json` | General finite upper bound and its asymptotic consequence |

Each configuration is submitted separately, using the same public repository
and full 40-character commit SHA. The project directory is the repository
root, and the metadata file is `formalization.yaml`.

The independent Challenges define coverage and the bound formulas using only
Mathlib imports. Their deliberate proof holes specify the statements.
Solutions are compiled separately and do not import the Challenges. The
configurations permit only `propext`, `Classical.choice`, and `Quot.sound`,
enable NanoDa, and provide no replaceable definition bodies.

## Static checks

Run the source-size and module-header scan with Python 3:

```sh
python3 scripts/check-lean-sources.py
```

For the metadata and configuration checks, use an external checkout of
[PalomarSubmission at the recorded revision](https://github.com/PalomarRegistry/PalomarSubmission/tree/ad5db9e7ff8b17523d73aeb244aaeabcde810c64):

```sh
python3 scripts/validate-submission.py --palomar-source /path/to/PalomarSubmission
```

The second command requires PyYAML. It uses the pinned official validator and
also enforces the source-type vocabulary in the current submission standard.
These are static checks; they do not run Lean or the independent kernels.
The source scanner is retained from
[the official starter](https://github.com/PalomarRegistry/PalomarTemplate/tree/2891de4c48955af824969a263d31b25e7a9a1406),
under Apache-2.0. Metadata uses schema v0.4.

The repository pins Lean 4.35.0, which meets the current minimum release
requirement. All retained Lean sources use modules and satisfy the source
length limits. The Challenges also satisfy their stricter size and import
limits. The root licence was classified as Apache-2.0; the
[classification record](../verification/licensee.json) preserves the original
check and identifies the unchanged licence and current metadata declaration.

## Verification and registration

The [build guide](BUILD.md) and [verification record](../verification.json)
describe the completed local checks. Local verification is distinct from
Palomar's protected Linux verification and editorial review.

Submit the public repository and chosen commit at
[Palomar's submission page](https://submit.palomar-registry.org/), selecting
the appropriate Comparator configuration. Palomar verifies the submitted
snapshot on its own public GitHub Actions infrastructure. The human submission form starts Palomar
verification after authentication. For automated API submission, the
[agent protocol](https://submit.palomar-registry.org/llms.txt) additionally
requires a successful full preflight at the exact commit before intake.
The included manually triggered workflow supplies that preflight; it has
not been run. An agent must not use the human browser-authentication route.

After verification, Palomar presents an automated review. Registration is a
subsequent choice made after reading that review. The metadata records the
mathematical sources, substantial AI assistance, and the extent of recorded
review; agent review is not human peer review.

The informal mathematical account is [INFORMAL_STATEMENT.md](INFORMAL_STATEMENT.md).
It explains both selected claims and their relation to the construction.
