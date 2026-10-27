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

def FiniteBound : Prop :=
  ∀ m : Nat, 12 ≤ m → ∀ a : Nat, 2 ≤ a → a ≤ m →
    ∃ w : Almanac.Word (m + 2), Almanac.IsSuperpermutation (m + 2) w ∧
      (w.length : ℚ) ≤ SuperpermutationUpper.bound m a

def WordAtMost (n value : Nat) : Prop :=
  ∃ w : Almanac.Word n, Almanac.IsSuperpermutation n w ∧ w.length ≤ value

theorem finite_bound : FiniteBound := by
  intro m hm a ha ham
  obtain ⟨w, hw, hlen⟩ := SuperpermutationUpper.finite_bound m hm a ha ham
  exact ⟨w, (covers_iff w).mp hw, hlen⟩

theorem word_at_most {n value : Nat}
    (h : ∃ w : List (Fin n), SuperpermutationUpper.Covers w ∧ w.length ≤ value) :
    WordAtMost n value := by
  obtain ⟨w, hw, hlen⟩ := h
  exact ⟨w, (covers_iff w).mp hw, hlen⟩

/-- The full upper package. The numerical clauses are existence theorems,
not explicit uploaded words, and do not request finite word-record entries. -/
def CompleteClaim : Prop :=
  FiniteBound ∧ Almanac.AsymptoticUpper (926683 / 1814400) ∧
  WordAtMost 14 93905133768 ∧ WordAtMost 15 1401329128342 ∧
  WordAtMost 16 22320881220264 ∧ WordAtMost 17 377963186649048 ∧
  WordAtMost 18 6779662770937056 ∧ WordAtMost 19 128414015952702480 ∧
  WordAtMost 20 2561133914781361920

theorem complete_claim : CompleteClaim := by
  exact ⟨finite_bound, asymptotic_upper,
    word_at_most SuperpermutationUpper.word_14,
    word_at_most SuperpermutationUpper.word_15,
    word_at_most SuperpermutationUpper.word_16,
    word_at_most SuperpermutationUpper.word_17,
    word_at_most SuperpermutationUpper.word_18,
    word_at_most SuperpermutationUpper.word_19,
    word_at_most SuperpermutationUpper.word_20⟩

end AlmanacAdapter
