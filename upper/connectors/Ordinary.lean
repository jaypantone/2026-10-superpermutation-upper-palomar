module

public import upper.partition.Validity
public import upper.Iteration

@[expose] public section

/-! The ordinary component of the native connector family. Its incidence is
the literal full-chart case of SafeIncidence, with the inherited soundness
theorem giving incidence in every designated completion trail. -/
namespace SuperpermutationUpperBound.Native14.Connectors.Ordinary
open CircleTransport
open SuperpermutationUpperBound.Partition
open Certificate

def circle (x y : List Nat) : List Nat := y.map (Partition.relabelSeven x)

def circles : List (List Nat) := EmptyLoops.halfarAncestors.flatMap
  (fun x=>EmptyLoops.blockFEmpty.map (circle x))

theorem circle_mem {x y : List Nat} (hx : x∈EmptyLoops.halfarAncestors)
    (hy : y∈EmptyLoops.blockFEmpty) : circle x y∈circles :=
  List.mem_flatMap.mpr ⟨x,hx,List.mem_map.mpr ⟨y,hy,rfl⟩⟩

theorem circles_cases {c : List Nat} (hc : c∈circles) :
    ∃x∈EmptyLoops.halfarAncestors,∃y∈EmptyLoops.blockFEmpty,c=circle x y := by
  obtain ⟨x,hx,hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨y,hy,he⟩ := List.mem_map.mp hc
  exact ⟨x,hx,y,hy,he.symm⟩

theorem circle_length (x : List Nat) {y : List Nat} (hy : y∈EmptyLoops.blockFEmpty) :
    (circle x y).length=11 := by
  simpa only [circle,List.length_map,List.length_range] using
    (EmptyLoops.blockFEmpty_perm y hy).length_eq

theorem circles_length : circles.length=46368 := by
  simp only [circles,List.length_flatMap,List.length_map,EmptyLoops.blockFEmpty_length,
    List.map_const',List.sum_replicate,EmptyLoops.halfarAncestors_length]
  decide

theorem circles_valid : CircleFamilyValid 11 circles := by
  intro c hc
  obtain ⟨x,hx,y,hy,rfl⟩ := circles_cases hc
  refine ⟨circle_length x hy,?_⟩
  exact ((EmptyLoops.blockFEmpty_perm y hy).nodup_iff.mpr List.nodup_range).map
    (Partition.relabelSeven_injective (EmptyLoops.halfarAncestors_perm x hx))

theorem circles_support : Iteration.CircleSupport 0 circles := by
  intro c hc a ha
  obtain ⟨x,hx,y,hy,rfl⟩ := circles_cases hc
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  have hb11 : b<11 := List.mem_range.mp ((EmptyLoops.blockFEmpty_perm y hy).mem_iff.mp hb)
  have hm : Partition.relabelSeven x b∈(List.range 12).map (Partition.relabelSeven x) :=
    List.mem_map.mpr ⟨b,List.mem_range.mpr (by omega),rfl⟩
  have hb12 : Partition.relabelSeven x b<12 := List.mem_range.mp
    ((Partition.relabelSeven_range12_perm (EmptyLoops.halfarAncestors_perm x hx)).mem_iff.mp hm)
  constructor <;> omega

/-- One ordinary circle serves every one of its parent's eleven completion
ports. Relabeling fixes the active and satellite letters. -/
theorem safeIncidence (x : List Nat) {y : List Nat}
    (hy : y∈EmptyLoops.blockFEmpty) (j : Fin 11) :
    SafeIncidence ((fullChart y 11 12).map (Row.map (Partition.relabelSeven x)))
      13 j (circle x y) := by
  refine Or.inr ⟨circle x y,11,12,?_,?_⟩
  · exact CyclicEq.refl (List.length_pos_iff.mp (by rw [circle_length x hy];decide))
  · simpa only [circle,Partition.relabelSeven_fixed x (by decide : 7≤11),
      Partition.relabelSeven_fixed x (by decide : 7≤12)] using
      (Partition.fullChart_map (Partition.relabelSeven x) y 11 12).symm

theorem cover {x y : List Nat} (hx : x∈EmptyLoops.halfarAncestors)
    (hy : y∈EmptyLoops.blockFEmpty) (j : Fin 11) :
    ∃c∈circles,SafeIncidence
      ((fullChart y 11 12).map (Row.map (Partition.relabelSeven x))) 13 j c :=
  ⟨circle x y,circle_mem hx hy,safeIncidence x hy j⟩

end SuperpermutationUpperBound.Native14.Connectors.Ordinary
