module

public import upper.review.SparsePointers

@[expose] public section

/-! Source-row prefix annotations are checked once by a linear recurrence.
Their semantic soundness avoids recomputing a prefix sum for every incidence. -/
namespace SuperpermutationUpperBound.Native14.Certificate
open Transport

/-- One integer annotation for every actual source row, in its original order. -/
def sourcePrefixCheck {α : Type} : List (Row α) → List Int → Int → Bool
  | [], [], _ => true
  | r :: rs, e :: es, start =>
      decide (e = start) && sourcePrefixCheck rs es (start + 1 - (r.charge : Int))
  | _, _, _ => false

theorem signedExcess_cons (r : Row α) (rs : List (Row α)) :
    signedExcess (r :: rs) = 1 - (r.charge : Int) + signedExcess rs := by
  simp only [signedExcess, List.length_cons, List.map_cons, List.sum_cons,
    Nat.cast_add, Nat.cast_one]
  omega

/-- Every successful annotation lookup is the signed excess of the actual
source prefix, relative to the initial ledger. -/
theorem sourcePrefixCheck_sound {α : Type} {rs : List (Row α)} {es : List Int}
    {start : Int} (h : sourcePrefixCheck rs es start = true)
    (i : Nat) (hi : i < rs.length) :
    signedExcess (rs.take i) = es.getD i 0 - start := by
  induction rs generalizing es start i with
  | nil => simp at hi
  | cons r rs ih =>
      cases es with
      | nil => simp [sourcePrefixCheck] at h
      | cons e es =>
          have hh := Bool.and_eq_true_iff.mp h
          have he : e = start := of_decide_eq_true hh.1
          subst e
          cases i with
          | zero => simp [signedExcess]
          | succ i =>
              have hir : i < rs.length := by simpa using hi
              have hr := ih hh.2 i hir
              simp only [List.take_succ_cons, signedExcess_cons, List.getD_cons_succ]
              omega

/-- A checked source index yields a literal row occurrence with its cached
ledger. The row itself is selected from the authoritative source walk. -/
theorem sourcePrefix_occurrence {α : Type} {rs : List (Row α)} {es : List Int}
    (h : sourcePrefixCheck rs es 0 = true) (i : Nat) (hi : i < rs.length) :
    ∃ pre post, rs = pre ++ rs[i] :: post ∧ signedExcess pre = es.getD i 0 := by
  refine ⟨rs.take i, rs.drop (i+1), ?_, ?_⟩
  · have hd := List.take_append_drop i rs
    rw [List.drop_eq_getElem_cons hi] at hd
    exact hd.symm
  · simpa only [sub_zero] using sourcePrefixCheck_sound h i hi

end SuperpermutationUpperBound.Native14.Certificate
