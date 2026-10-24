module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Fin.Basic

/-!
# An upper bound for superpermutations

A superpermutation on `K` symbols is a finite word containing each permutation
as a contiguous factor. We prove the existence of such words with length at
most `K! + (K-1)! + (K-2)! + (926683/1814400 + epsilon)(K-3)!` for all sufficiently
large `K`. The coefficient is about 0.510738, improving the earlier 43/80
coefficient. The finite theorem gives an explicit parameter bound for every
`K >= 14`; seven numerical consequences are included.

The construction uses a finite fourteen-symbol base construction, a verified
connector cover, and a transport theorem to increase the alphabet. Its finite
certificates are checked by ordinary Lean proofs, without `native_decide`.
The assertions here concern actual words, with no construction hypothesis.

This statement module imports only Mathlib. Deliberate proof holes specify the
claims to be compared with the independently built `Solution` module; they are
not part of the submitted proofs.
-/

@[expose] public section
namespace SuperpermutationUpper

/-- Every permutation of the alphabet occurs as a contiguous factor of `w`.
A length-`K` list without repetitions over `Fin K` is exactly a permutation. -/
def Covers {K : Nat} (w : List (Fin K)) : Prop :=
  ∀ p : List (Fin K), p.length = K → p.Nodup →
    ∃ u v : List (Fin K), w = u ++ p ++ v

/-- The first three factorial terms, regarded as a rational number. -/
def F3 (K : Nat) : ℚ :=
  (Nat.factorial K : ℚ) + (Nat.factorial (K - 1) : ℚ) +
    (Nat.factorial (K - 2) : ℚ)

/-- Explicit construction cost for `m+2` symbols and a joining parameter `a`.
The finite theorem assumes `12 <= m` and `2 <= a <= m`. Subtractions inside
natural-number casts are natural subtraction; these assumptions prevent
truncation in each such subtraction. All divisions are rational. -/
def bound (m a : Nat) : ℚ :=
  F3 (m + 2) + (926683 / 1814400 : ℚ) * ((m - 1).factorial : ℚ) +
    ((a - 2 : Nat) : ℚ) * (30571 / 1814400 : ℚ) * ((m - 1).factorial : ℚ) /
      ((m - 1 : Nat) : ℚ) +
    ((m - a : Nat) : ℚ) * min
      ((30571 / 1814400 : ℚ) * ((m - 1).factorial : ℚ) / ((m - 1 : Nat) : ℚ))
      (((m + 1).factorial : ℚ) / ((a + 1).factorial : ℚ))

/-- A uniform finite upper bound, with a freely chosen joining parameter. -/
theorem finite_bound :
    ∀ m : Nat, 12 ≤ m → ∀ a : Nat, 2 ≤ a → a ≤ m →
      ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ bound m a := by
  sorry

/-- The asymptotic upper coefficient is at most `926683/1814400`.
The positive rational epsilon formulation fixes the precise meaning of the
asymptotic assertion without needing to define a minimum word length. -/
theorem asymptotic_bound :
    ∀ ε : ℚ, 0 < ε → ∃ N : Nat, 14 ≤ N ∧
      ∀ K : Nat, N ≤ K → ∃ w : List (Fin K), Covers w ∧
        (w.length : ℚ) ≤ F3 K +
          ((926683 : ℚ) / 1814400 + ε) * ((K - 3).factorial : ℚ) := by
  sorry

/-- A fourteen-symbol word of length at most 93,905,133,768 exists. -/
theorem word_14 :
    ∃ w : List (Fin 14), Covers w ∧ w.length ≤ 93905133768 := by
  sorry

/-- A fifteen-symbol word of length at most 1,401,329,128,342 exists. -/
theorem word_15 :
    ∃ w : List (Fin 15), Covers w ∧ w.length ≤ 1401329128342 := by
  sorry

/-- A sixteen-symbol word of length at most 22,320,881,220,264 exists. -/
theorem word_16 :
    ∃ w : List (Fin 16), Covers w ∧ w.length ≤ 22320881220264 := by
  sorry

/-- A seventeen-symbol word of length at most 377,963,186,649,048 exists. -/
theorem word_17 :
    ∃ w : List (Fin 17), Covers w ∧ w.length ≤ 377963186649048 := by
  sorry

/-- An eighteen-symbol word of length at most 6,779,662,770,937,056 exists. -/
theorem word_18 :
    ∃ w : List (Fin 18), Covers w ∧ w.length ≤ 6779662770937056 := by
  sorry

/-- A nineteen-symbol word of length at most 128,414,015,952,702,480 exists. -/
theorem word_19 :
    ∃ w : List (Fin 19), Covers w ∧ w.length ≤ 128414015952702480 := by
  sorry

/-- A twenty-symbol word of length at most 2,561,133,914,781,361,920 exists. -/
theorem word_20 :
    ∃ w : List (Fin 20), Covers w ∧ w.length ≤ 2561133914781361920 := by
  sorry

end SuperpermutationUpper
