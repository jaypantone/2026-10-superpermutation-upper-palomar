module

public import upper.partition.FiniteSort

@[expose] public section

/-! A compact kernel-checkable cyclic-block inventory. Sorting literal rotated
bases proves coverage without enumerating the final 39,916,800-row expansion. -/
namespace SuperpermutationUpperBound.Native14.Partition

def canonicalBase (x : List Nat) : List Nat := rot x (x.idxOf 0)

def canonicalInventory (rs : List (Row Nat)) : List (List Nat) :=
  sortBlocks 13 (rs.map (fun r => canonicalBase r.base))

theorem canonicalBase_cyclicEq {x : List Nat} (hx : x ≠ []) :
    CyclicEq x (canonicalBase x) := CyclicEq.of_rot hx _

theorem cyclicEq_of_canonicalBase_eq {x y : List Nat}
    (hx : x ≠ []) (hy : y ≠ []) (h : canonicalBase x = canonicalBase y) :
    CyclicEq x y := by
  have hc := canonicalBase_cyclicEq hx
  rw [h] at hc
  exact hc.trans (canonicalBase_cyclicEq hy).symm

/-- The certificate compares all normalized cyclic bases, not only their counts. -/
theorem blockRefines_of_canonicalInventory_eq {rs ts : List (Row Nat)}
    (hr : ∀ r ∈ rs, r.Valid) (ht : ∀ t ∈ ts, t.Valid)
    (h : canonicalInventory rs = canonicalInventory ts) : BlockRefines rs ts := by
  intro r hrmem
  have hm : canonicalBase r.base ∈ canonicalInventory rs := by
    apply (mem_sortBlocks _ _ _).mpr
    exact List.mem_map_of_mem hrmem
  rw [h] at hm
  obtain ⟨t, htmem, htr⟩ := List.mem_map.mp ((mem_sortBlocks _ _ _).mp hm)
  exact ⟨t, htmem, cyclicEq_of_canonicalBase_eq
    (row_base_nonempty (ht t htmem)) (row_base_nonempty (hr r hrmem)) htr⟩

/-- Sorting certificates also establish the reverse refinement. -/
theorem blockRefines_pair_of_canonicalInventory_eq {rs ts : List (Row Nat)}
    (hr : ∀ r ∈ rs, r.Valid) (ht : ∀ t ∈ ts, t.Valid)
    (h : canonicalInventory rs = canonicalInventory ts) :
    BlockRefines rs ts ∧ BlockRefines ts rs :=
  ⟨blockRefines_of_canonicalInventory_eq hr ht h,
    blockRefines_of_canonicalInventory_eq ht hr h.symm⟩

end SuperpermutationUpperBound.Native14.Partition
