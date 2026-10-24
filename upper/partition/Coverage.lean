module

public import upper.partition.SeedCoverage
public import upper.partition.BlockCoverage

@[expose] public section

/-! The native n14 partition covers every ordinary cyclic block. The finite
certificates certify only 5040 blocks at a time; every larger step is semantic
transport, relabeling, and replacement of the same represented cyclic blocks. -/
namespace SuperpermutationUpperBound.Native14.Partition
open SuperpermutationUpperBound.Partition
open Certificate

theorem template_final_refines :
    BlockRefines (extendRange (fullChart (List.range 7) 7 12) 8 4) localRows := by
  have h₁ := BlockRefines.transport templateBlockRows_refines
    (fun r hr => (templateBlockRows_basedOn r hr).1)
    (fun r hr => (completeBlockRows_basedOn r hr).1) 11
  have h₂ := filledCharts_refines_transport blockRows EmptyLoops.blockFEmpty 11 12
    (fun r hr => (blockRows_basedOn r hr).1) (by
      intro x hx
      exact (fullAccounting_basedOn EmptyLoops.blockFEmpty_perm
        (by decide : 0<11) (by decide : 11≤12)
        (Row.mk x 12 x.length) (List.mem_map_of_mem hx)).1)
  exact h₁.trans h₂

theorem ancestor_final_refines {x : List Nat} (hx : x.Perm (List.range 7)) :
    BlockRefines (extendRange (fullChart x 7 12) 8 4)
      (localRows.map (Row.map (relabelSeven x))) := by
  have h := BlockRefines.map template_final_refines (relabelSeven x)
  have hchart := fullChart_map (relabelSeven x) (List.range 7) 7 12
  rw [relabelSeven_range hx, relabelSeven_fixed x (by decide : 7≤7),
    relabelSeven_fixed x (by decide : 7≤12)] at hchart
  rw [hchart, extendRange_map]
  · exact h
  · intro j hj
    exact relabelSeven_fixed x (by omega)

/-- Every permutation of the twelve ordinary letters is represented by an
actual native row, with no model-specific premise on that permutation. -/
theorem nativeRows_complete : BlockComplete (List.range 12) nativeRows := by
  have hc := extendRange_complete completeSeedRows_complete completeSeedRows_basedOn
    (by decide : 0<8) 4 (by decide : 8+4≤12)
  apply BlockRefines.complete (rs := extendRange completeSeedRows 8 4) _ hc
  rw [completeSeedRows, extendRange_append, extendRange_flatMap]
  apply BlockRefines.append
  · exact BlockRefines.refl (fun r hr =>
      (extendRange_basedOn seedRows_basedOn 4 (by decide : 8+4≤12) r hr).1)
  · apply BlockRefines.flatMap
    intro x hx
    exact ancestor_final_refines (EmptyLoops.halfarAncestors_perm x hx)

end SuperpermutationUpperBound.Native14.Partition
