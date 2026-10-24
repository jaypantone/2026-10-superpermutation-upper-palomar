module

public import upper.partition.Canonical
public import Mathlib.Data.List.Permutation

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Partition

/-- One canonical representative of every cyclic eight-letter permutation. -/
def canonicalSeedRows : List (Row Nat) :=
  (List.permutations' [1,2,3,4,5,6,7]).map (fun x => Row.mk (0::x) 12 8)


/-- Every eight-letter cyclic permutation has a canonical zero-first representative. -/
theorem canonicalSeedRows_complete : BlockComplete (List.range 8) canonicalSeedRows := by
  intro x hx
  have hz : 0∈x := hx.mem_iff.mpr (by decide)
  obtain ⟨a,b,rfl,_⟩ := List.eq_append_cons_of_mem hz
  have hc : CyclicEq (a++0::b) (0::(b++a)) := by
    have h := CyclicEq.of_rot (x:=a++0::b) (by simp) a.length
    simpa only [rot_append_length, List.cons_append] using h
  have hp : (b++a).Perm [1,2,3,4,5,6,7] :=
    (List.perm_cons 0).mp (hc.perm.symm.trans hx)
  refine ⟨Row.mk (0::(b++a)) 12 8, ?_, hc.symm⟩
  exact List.mem_map.mpr ⟨b++a,List.mem_permutations'.mpr hp,rfl⟩

theorem canonicalSeedRows_basedOn : BasedOn (List.range 8) 12 canonicalSeedRows := by
  intro r hr
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
  have hp : (0::x).Perm (List.range 8) := (List.mem_permutations'.mp hx).cons 0
  have hl : (0::x).length=8 := hp.length_eq
  have hs : 12∉0::x := fun hm => by have hh := List.mem_range.mp (hp.mem_iff.mp hm); omega
  exact ⟨⟨hp.nodup_iff.mpr List.nodup_range,hs,(by change 1≤8; decide),(by change 8≤(0::x).length; omega)⟩, hp,rfl,
    Or.inl hl.symm⟩

end SuperpermutationUpperBound.Native14.Partition
