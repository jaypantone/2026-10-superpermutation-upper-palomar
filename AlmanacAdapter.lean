import AlmanacDefs
import Solution

/-! Bridges from the independently stated Palomar result to the public
Superpermutation Almanac definitions. No mathematical hypothesis is added. -/

namespace AlmanacAdapter

theorem covers_iff {n : Nat} (w : Almanac.Word n) :
    SuperpermutationUpper.Covers w ↔ Almanac.IsSuperpermutation n w := by
  constructor
  · intro h p hnd hlen
    obtain ⟨u, v, huv⟩ := h p hlen hnd
    exact ⟨u, v, huv.symm⟩
  · intro h p hlen hnd
    obtain ⟨u, v, huv⟩ := h p hnd hlen
    exact ⟨u, v, huv.symm⟩

@[simp] theorem fact_eq (n : Nat) : Almanac.fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Almanac.fact, Nat.factorial_succ, ih]

theorem asymptotic_upper : Almanac.AsymptoticUpper (926683 / 1814400) := by
  intro ε hε
  obtain ⟨N, _, hN⟩ := SuperpermutationUpper.asymptotic_bound ε hε
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨w, hw, hlen⟩ := hN n hn
  refine ⟨w, (covers_iff w).mp hw, ?_⟩
  simpa [Almanac.asymptoticForm, SuperpermutationUpper.F3] using hlen

end AlmanacAdapter
