module

public import upper.partition.Validity
public import upper.partition.ExtensionCounts

@[expose] public section

/-! Bounded certificates for block coverage. Each witness is an index into the
actual target list. No sorting algorithm, trusted hash, or uniqueness claim is
needed: matching canonical bases supplies precisely the required refinement. -/
namespace SuperpermutationUpperBound.Native14.Partition
open SuperpermutationUpperBound.Partition

/-- Check an equally long list of target indices against the source rows. -/
def blockWitnessCheck (target : List (Row Nat)) :
    List (Row Nat) → List Nat → Bool
  | [], [] => true
  | r::rs, i::is =>
      match target[i]? with
      | none => false
      | some t => decide (canonicalBase t.base = canonicalBase r.base) &&
          blockWitnessCheck target rs is
  | _, _ => false

theorem blockWitnessCheck_sound {source target : List (Row Nat)} {indices : List Nat}
    (hs : ∀ r ∈ source, r.Valid) (ht : ∀ t ∈ target, t.Valid)
    (hc : blockWitnessCheck target source indices = true) :
    BlockRefines source target := by
  induction source generalizing indices with
  | nil => intro r hr; simp at hr
  | cons r rs ih =>
      cases indices with
      | nil => simp [blockWitnessCheck] at hc
      | cons i is =>
          cases hget : target[i]? with
          | none => simp [blockWitnessCheck, hget] at hc
          | some t =>
              have hh : canonicalBase t.base = canonicalBase r.base ∧
                  blockWitnessCheck target rs is = true := by
                simpa only [blockWitnessCheck, hget, Bool.and_eq_true_iff,
                  decide_eq_true_eq] using hc
              obtain ⟨hi, he⟩ := List.getElem?_eq_some_iff.mp hget
              have htm : t ∈ target := he ▸ List.getElem_mem hi
              have hrest := ih (fun q hq => hs q (List.mem_cons_of_mem _ hq)) hh.2
              intro q hq
              rcases List.mem_cons.mp hq with hq | hq
              · subst q
                exact ⟨t, htm, cyclicEq_of_canonicalBase_eq
                  (row_base_nonempty (ht t htm))
                  (row_base_nonempty (hs r (by simp))) hh.1⟩
              · exact hrest q hq

theorem blockWitnessCheck_slice_sound {source target : List (Row Nat)}
    {start count : Nat} {indices : List Nat}
    (hs : ∀ r ∈ source, r.Valid) (ht : ∀ t ∈ target, t.Valid)
    (hc : blockWitnessCheck target ((source.drop start).take count) indices = true) :
    BlockRefines ((source.drop start).take count) target :=
  blockWitnessCheck_sound
    (fun r hr => hs r (List.mem_of_mem_drop (List.mem_of_mem_take hr))) ht hc

/-- Consecutive checked slices join without recomputing either certificate. -/
theorem blockRefines_drop_step {source target : List (Row Nat)} (start count : Nat)
    (hhead : BlockRefines ((source.drop start).take count) target)
    (htail : BlockRefines (source.drop (start+count)) target) :
    BlockRefines (source.drop start) target := by
  intro r hr
  have hm : r ∈ (source.drop start).take count ∨
      r ∈ (source.drop start).drop count := by
    rw [← List.mem_append, List.take_append_drop]
    exact hr
  rcases hm with hm | hm
  · exact hhead r hm
  · exact htail r (by simpa only [List.drop_drop] using hm)

theorem blockRefines_drop_end {source target : List (Row Nat)} (start : Nat)
    (h : source.length ≤ start) : BlockRefines (source.drop start) target := by
  rw [List.drop_eq_nil_of_le h]
  intro r hr
  simp at hr

theorem templateBlockRows_length : templateBlockRows.length = 5040 := by
  unfold templateBlockRows
  rw [extendRange_length
    (fullChart_range_basedOn (List.Perm.refl _) (by decide : 7<12)) 3 (by decide),
    fullChart_length]
  decide

end SuperpermutationUpperBound.Native14.Partition
