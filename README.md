# A smaller upper bound for superpermutations

The Almanac batch entry point is [AlmanacSolution.lean](AlmanacSolution.lean), with one result per theorem in `AlmanacSubmission`. See [the Almanac submission guide](docs/ALMANAC.md) for the selected results, template coverage, validation, and submission steps. The original Palomar configuration and proof development are retained separately below.

A superpermutation on n symbols contains every permutation of those symbols
as a contiguous factor. Write S(n) for its minimum possible length and
F₃(n) = n! + (n−1)! + (n−2)!. This repository proves

$$
S(n)\le F_3(n)+\left(\frac{926683}{1814400}+o(1)\right)(n-3)!.
$$

The coefficient is approximately **0.510738**, improving the **43/80**
coefficient of [Pantone's earlier construction](https://github.com/jaypantone/superperm-upper-43-80).
It is still larger than 1/2. The result comes from a different finite
selection and a smaller connector cover within that construction. It does
not determine the optimum asymptotic coefficient.

**AI disclosure.** The research presented here, the Lean formalization, and this document were generated entirely by AI systems under Jay Pantone's direction. The inherited mathematical work and software retain their original credits. Independent AI review is not human peer review.

Start with the [informal statement](docs/INFORMAL_STATEMENT.md), the
[paper](papers/upper/upper-bounds.pdf), or the
[independent formal statement](Challenge.lean). The theorem has an explicit
finite form for every n ≥ 14, with a parameter that controls how the final
pieces are joined. [Solution.lean](Solution.lean) proves that form, its
asymptotic consequence, and seven numerical corollaries.

## Original Palomar comparison

[comparator.json](comparator.json) selects two theorems in the namespace
`SuperpermutationUpper`:

| Declaration | Claim |
|---|---|
| `finite_bound` | An actual covering word exists within the explicit parameter bound for every alphabet size at least 14 |
| `asymptotic_bound` | Every positive rational epsilon eventually permits coefficient 926683/1814400 + epsilon |

The numerical corollaries remain in the repository but are not selected
for this submission.

`Challenge.lean` gives the complete definitions and statement types using
only Mathlib imports. Its deliberate proof holes specify the claims to be
checked. `Solution.lean` repeats the definitions and types, supplies their
proofs, and does not import `Challenge.lean`. Comparator builds the two
modules in separate environments. The holes in the Challenge are not proof
assumptions in the Solution.

The supporting proof is included in full. It verifies the finite selection
and every connector incidence, transports the construction to larger
alphabets, and assembles covering words. The current 681-module library
builds in Lean 4.35.0, and NanoDa independently accepts the complete exported
proofs of both selected results and all seven numerical corollaries using
four workers. Both checks concern
the revised sources. The selected results use only `propext`,
`Classical.choice`, and `Quot.sound`. No theorem in this upper proof uses
`native_decide`; the historical namespace `Native14` refers to the finite
base construction.

The [compatibility note](docs/PORTING.md) records the six proof-body
changes made for independent-kernel verification. Statements and certificate
data are unchanged.

The [verification record](verification.json) binds the current build and
complete NanoDa replay to source, object, compiler, checker, and export hashes.
It also preserves the earlier source snapshot's successful statement
comparison and fresh Lean replay. Those earlier checks have not been repeated
on the revised sources. All local diagnostics are unsandboxed macOS checks;
the protected Linux Palomar workflow remains unrun. No mathematical bound
changed.

See the [build guide](docs/BUILD.md) for shared storage, the local resource
controls, and reproduction.

This repository is prepared for submission to Palomar. Preparation and a
local build are not Palomar registration; registration additionally requires
the complete Comparator, Lean replay, independent-kernel replay, and
editorial workflow. See [formalization.yaml](formalization.yaml) for
provenance and the recorded verification status.

The [comparison with announced results](docs/RELATED_WORK.md) gives
the relevant contributions of Halfar, Echols, and Theo H. The bounds and
words here are not presented as a list of current records.

## Numerical consequences

These bounds assert existence of words; no enormous word files are required
to prove them.

| n | Upper bound on S(n) |
|---:|---:|
| 14 | 93,905,133,768 |
| 15 | 1,401,329,128,342 |
| 16 | 22,320,881,220,264 |
| 17 | 377,963,186,649,048 |
| 18 | 6,779,662,770,937,056 |
| 19 | 128,414,015,952,702,480 |
| 20 | 2,561,133,914,781,361,920 |

## Four explicit words

The repository also contains these complete superpermutations on smaller
alphabets. They are separate finite constructions, checked directly for
permutation coverage, rather than instances of the n ≥ 14 theorem.

| Symbols | Length | File |
|---:|---:|---|
| 10 | 4,034,857 | [Plain text](words/10/superpermutation-10-4034857.txt) |
| 11 | 43,930,548 | [Plain text](words/11/superpermutation-11-43930548.txt) |
| 12 | 522,737,007 | [XZ](words/12/superpermutation-12-522737007.txt.xz) |
| 13 | 6,747,802,736 | [XZ](words/13/superpermutation-13-6747802736.txt.xz) |

The [word guide](words/README.md) explains the encoding, checksums,
compression settings, checker, and attribution. The [coverage record](words/coverage.json)
is preserved from the complete scans performed on 9 October 2026. These
program checks are not among the two Lean claims selected for Palomar.
The files and their recorded packed hashes are unchanged from that release.

## Layout

- `Challenge.lean`, `Solution.lean`, `AxiomCheck.lean`: statements, proofs,
  and assumption-reporting entry point.
- `upper/`: the improved finite construction, certificates, and consequences.
- `SuperpermutationUpperBound/`: the inherited construction and transport library.
- `UpperBoundProof/Statement.lean`: internal definitions inherited by that library.
- `papers/`: mathematical exposition, TeX source, and PDF.
- `words/` and `tools/`: explicit words and reproducible checking programs.
- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: pinned Lean build inputs.
- `formalization.yaml` and `comparator.json`: Palomar metadata and exact claims.

Compilers, Mathlib copies, build products, search histories, and unsuccessful
experiments are excluded. The many small certificate modules are required
parts of the proof. See [NOTICE](NOTICE) for attribution and [LICENSE](LICENSE)
for licensing. This package presents the existing improved upper bound;
it makes no additional numerical improvement claim.
