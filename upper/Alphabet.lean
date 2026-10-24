module

public import SuperpermutationUpperBound.Partition.Basic
public import SuperpermutationUpperBound.Completion.Counts
public import SuperpermutationUpperBound.Completion.Alphabet
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! The alphabet for the native n14 base. Adapted from Pantone's SprintFamily. -/
namespace SuperpermutationUpperBound.Native14.Alphabet

/-- Reserve12 and13 as satellite and completion letters. Subsequent ordinary
letters are14,15,..., so the full word alphabet stays an initial Nat interval. -/
def alphabet : Nat → List Nat
  | 0 => (List.range 12)
  | k + 1 => (k + 14) :: alphabet k

@[simp] theorem alphabet_length (k : Nat) : (alphabet k).length = k + 12 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [alphabet, ih, Nat.add_assoc]

theorem alphabet_lt (k : Nat) : ∀ a ∈ alphabet k, a < k + 14 := by
  induction k with
  | zero => decide
  | succ k ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have := ih a ha; omega

theorem alphabet_fresh (k : Nat) : k + 14 ∉ alphabet k := by
  intro h
  have := alphabet_lt k (k + 14) h
  omega

theorem alphabet_nodup (k : Nat) : (alphabet k).Nodup := by
  induction k with
  | zero => decide
  | succ k ih => exact List.nodup_cons.mpr ⟨alphabet_fresh k, ih⟩

theorem alphabet_satellite (k : Nat) : 12 ∉ alphabet k := by
  induction k with
  | zero => decide
  | succ k ih => simpa [alphabet] using And.intro (by omega : 12 ≠ k + 14) ih

theorem alphabet_final (k : Nat) : 13 ∉ alphabet k := by
  induction k with
  | zero => decide
  | succ k ih => simpa [alphabet] using And.intro (by omega : 13 ≠ k + 14) ih

theorem alphabet_nonempty (k : Nat) : alphabet k ≠ [] := by
  have h := alphabet_length k
  intro he
  rw [he] at h
  simp at h

/-- The entire alphabet, including the fixed satellite and final letter,
contains exactly the symbols0,...,k+13. -/
theorem full_alphabet_perm (k : Nat) : (13 :: (alphabet k ++ [12])).Perm (List.range (k + 14)) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hswap : (13 :: ((k + 14) :: alphabet k ++ [12])).Perm
        ((k + 14) :: 13 :: (alphabet k ++ [12])) := List.Perm.swap ..
    change (13 :: ((k + 14) :: alphabet k ++ [12])).Perm _
    apply (hswap.trans (ih.cons (k + 14))).trans
    rw [show k + 1 + 14 = (k + 14) + 1 by omega, List.range_succ (n := k + 14)]
    exact List.perm_append_comm (l₁ := [k + 14]) (l₂ := List.range (k + 14))

def stateAlphabet (k : Nat) : Finset Nat := (13 :: alphabet k).toFinset

theorem stateAlphabet_card (k : Nat) : (stateAlphabet k).card = k + 13 := by
  have hn : (13 :: alphabet k).Nodup := List.nodup_cons.mpr ⟨alphabet_final k, alphabet_nodup k⟩
  rw [stateAlphabet, List.toFinset_card_of_nodup hn]
  simp [Nat.add_assoc]

theorem stateAlphabet_mem (k : Nat) (a : Nat) :
    a ∈ stateAlphabet k ↔ a < k + 14 ∧ a ≠ 12 := by
  have hp := full_alphabet_perm k
  simp only [stateAlphabet, List.mem_toFinset, List.mem_cons]
  constructor
  · intro ha
    have hm : a ∈ 13 :: (alphabet k ++ [12]) := by
      rcases ha with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
    have hr : a ∈ List.range (k + 14) := hp.mem_iff.mp hm
    refine ⟨List.mem_range.mp hr, ?_⟩
    intro heq
    subst a
    simp only [show (12 : Nat) ≠ 13 by decide, false_or] at ha
    exact alphabet_satellite k ha
  · intro ⟨ha, hne⟩
    have hmem := hp.mem_iff.mpr (List.mem_range.mpr ha)
    simpa [hne] using hmem


end SuperpermutationUpperBound.Native14.Alphabet
