# Building and checking the proofs

The project pins Lean 4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`. All project proof sources are
included; the earlier results repository is a source citation, not a build
dependency.

## Lake build

With Elan installed, run these commands from a checkout:

```sh
lake exe cache get
lake build
```

Lake downloads the pinned dependencies and creates build outputs in `.lake`.
Use a checkout outside cloud-synchronized storage, and reuse matching expanded
dependencies where possible. The supplied local tools instead use `~/.elan`
and `~/Library/Caches/LeanShared`, with separate project build directories.

The Lake configuration limits each compiler to one Lean thread and a 4 GiB
Lean allocation budget. Lake may start several compilers concurrently; those
per-process settings do not impose an aggregate memory limit. Lean's allocation
budget is also distinct from total process memory.

## Verification

The `comparator*.json` files select the exact submitted claims. Each Challenge
and Solution pair declares the same names in separate environments; do not
import both into one module. `AxiomCheck.lean` reports the assumptions of the
selected theorems.

The current 681-module proof library passed a complete build and a
four-worker NanoDa replay of all nine general and numerical claims,
including the two selected for this submission. Statement comparison
and a separate Lean export replay passed on the earlier source snapshot.
Six subsequent proof-body changes preserve the statements and certificate
data; those two earlier checks have not been repeated on the revised source.
See [the porting note](PORTING.md) for the exact changes.

A successful Lake build checks the Lean proofs. Comparator additionally
compares the independent statements and checks their axioms; NanoDa provides
an independent kernel replay. The [verification record](../verification.json)
identifies the source snapshots, checks performed, and limitations.
Palomar's own verification and review are separate; see
[the submission guide](PALOMAR.md).

## Local checking tools

`tools/check.py` and `tools/local_compare.py` implement the recorded macOS
checking procedure using shared storage. Their guard permits one compiler per
project, samples aggregate process-group memory against an 8 GiB threshold,
and requires 15 GiB free disk. The default deadline is 300 seconds; the replay
tool accepts an explicit kernel deadline of at most 10,800 seconds. These
tools do not monitor host memory pressure, and their sampled watchdog is not
an operating-system memory cap. A timeout or resource stop is an incomplete
check.

The latest upper build and four-worker NanoDa replay used a separate
supervisor with a sampled 6 GiB aggregate memory threshold and continuous
host-pressure monitoring. Peak sampled memory was 4.4 GiB for the build and
3.9 GiB for NanoDa. Those additional safeguards are not implemented by the
historical tools above.
