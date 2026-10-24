# What changed for Palomar

The mathematical results come from the frozen October 2026 development at
`c9ccb6a0d9ddd1007fdce6efab50807ec47464b9`. This repository retains its exact
678-module upper-proof dependency closure. It adds independent statement,
solution, and axiom-reporting entry points, rather than importing a proposition
from the proof library into the submitted Challenge.

The port uses Lean 4.35's module system, public imports, and exposed public
declarations. The inherited module named `Challenge` is now
`UpperBoundProof.Statement`, leaving the root `Challenge.lean` for the
independent specification. One length-inequality proof in
`Partition/SeedBase.lean` now uses simplification with the same length equality.
`Assembly/ImbalanceCounts.lean` explicitly imports
`Mathlib.Algebra.BigOperators.Ring.Finset` for the existing `Nat.cast_sum`
lemma; that file's statements and proof bodies are unchanged. No theorem
statement changed in the port.

The 240 connector-certificate modules use `decide +kernel` for their 3,828
closed Boolean leaf checks. This avoids preliminary elaborator evaluation
while preserving ordinary kernel proof checking. Every witness integer,
offset, theorem statement, and assembly proof is unchanged; each leaf still
checks at most 32 incidences. Independent reverse comparison verified that
undoing the tactic substitution restores the previous files exactly.
[port-compatibility.json](../port-compatibility.json) records these changes and
the bounded timing comparison. It is a compilation improvement; every fresh
kernel replay still checks the certificate's computation.

Six further proof-body replacements address independent-kernel stack usage.
The five `Halfar0Parts.C00`–`C04` equalities and `BlockF0Parts.C00.rows_eq_suffix`
now unfold their suffix definitions and use `List.append_assoc`, instead of
normalizing their row data with `rfl`. Their theorem names, statements,
imports, definitions, and certificate data are unchanged. A failure was
isolated in `Halfar0Parts.C00.rows_eq_suffix`; the five analogous replacements
are preventive. The complete revised export of all nine selected claims
subsequently passed the four-worker NanoDa replay recorded below.

[source-provenance.json](../source-provenance.json) and
[port-compatibility.json](../port-compatibility.json) preserve the identities
and changes recorded for the original port. Their file hashes describe that
earlier snapshot. The additive
[proof compatibility record](../proof-compatibility.json) records the six later
proof replacements and their before/after hashes. Restoring the original port
therefore requires reversing these replacements as well; visibility directives
alone do not account for all proof changes.

[verification.json](../verification.json) records the complete current build
and four-worker NanoDa replay, alongside the preserved earlier targeted checks
and original full replay. The compatibility record's runtime note describes
its preparation stage; current status is given by the verification record.
A fresh Comparator run and fresh Lean export replay on the revised sources
have not been performed. Source comparison alone is not proof verification.

The paper's repository references were updated. The four word files and their
historical coverage records are unchanged. No search was repeated and no new
bound is claimed by this port.
