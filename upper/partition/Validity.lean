module

public import upper.partition.NativeRows

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Partition
open SuperpermutationUpperBound.Partition
open Certificate

theorem basedOn_append {alphabet : List Nat} {s : Nat} {rs ts : List (Row Nat)}
    (hr : BasedOn alphabet s rs) (ht : BasedOn alphabet s ts) :
    BasedOn alphabet s (rs++ts) := by
  intro r hm
  exact (List.mem_append.mp hm).elim (hr r) (ht r)

theorem seedRows_basedOn : BasedOn (List.range 8) 12 seedRows :=
  basedOn_append Halfar0.rows_basedOn Halfar1.rows_basedOn

theorem blockRows_basedOn : BasedOn (List.range 11) 12 blockRows :=
  basedOn_append (basedOn_append BlockF0.rows_basedOn BlockF1.rows_basedOn) BlockF2.rows_basedOn

theorem fullChart_basedOn {alphabet x : List Nat} {z s : Nat}
    (hp : x.Perm alphabet) (ha : alphabet.Nodup)
    (hz : z ∉ alphabet) (hs : s ∉ alphabet) (hsz : s ≠ z) :
    BasedOn (z::alphabet) s (fullChart x z s) := by
  intro r hr
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hr
  have hzx : z ∉ x := fun hm => hz (hp.mem_iff.mp hm)
  have hsx : s ∉ x := fun hm => hs (hp.mem_iff.mp hm)
  refine ⟨fullChartAt_valid (hp.nodup_iff.mpr ha) hzx hsx hsz j, ?_, rfl, Or.inl ?_⟩
  · exact ((rot_perm x j).append_right [z]).trans
      ((hp.append_right [z]).trans (by simpa using
        (List.perm_append_comm (l₁ := alphabet) (l₂ := [z]))))
  · simp

theorem fullChart_range_basedOn {x : List Nat} {n s : Nat}
    (hp : x.Perm (List.range n)) (hns : n < s) :
    BasedOn (List.range (n+1)) s (fullChart x n s) := by
  apply basedOn_perm_alphabet
    (fullChart_basedOn hp List.nodup_range (by simp) (by simp; omega) (by omega))
  rw [List.range_succ]
  simpa using (List.perm_append_comm (l₁ := [n]) (l₂ := List.range n))

theorem fullAccounting_basedOn {xs : List (List Nat)} {n : Nat}
    (hxs : ∀ x ∈ xs, x.Perm (List.range n)) (hn : 0<n) (hn12 : n≤12) :
    BasedOn (List.range n) 12 (fullAccounting xs) := by
  intro r hr
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
  have hp := hxs x hx
  have hl : x.length=n := by simpa using hp.length_eq
  have hs : 12∉x := fun hm => by have hh := List.mem_range.mp (hp.mem_iff.mp hm); omega
  refine ⟨⟨hp.nodup_iff.mpr List.nodup_range, hs, ?_, le_rfl⟩, hp, rfl, Or.inl rfl⟩
  change 1 ≤ x.length
  omega

theorem completeBlockRows_basedOn : BasedOn (List.range 11) 12 completeBlockRows :=
  basedOn_append blockRows_basedOn
    (fullAccounting_basedOn EmptyLoops.blockFEmpty_perm (by decide) (by decide))

theorem completeSeedRows_basedOn : BasedOn (List.range 8) 12 completeSeedRows := by
  apply basedOn_append seedRows_basedOn
  intro r hr
  obtain ⟨x,hx,hr⟩ := List.mem_flatMap.mp hr
  exact fullChart_range_basedOn (EmptyLoops.halfarAncestors_perm x hx) (by decide) r hr

theorem templateBlockRows_basedOn : BasedOn (List.range 11) 12 templateBlockRows := by
  exact extendRange_basedOn (fullChart_range_basedOn (List.Perm.refl _) (by decide : 7<12)) 3 (by decide)

theorem localRows_basedOn : BasedOn (List.range 12) 12 localRows := by
  apply basedOn_append (basedOn_transport_range blockRows_basedOn (by decide))
  intro r hr
  obtain ⟨x,hx,hr⟩ := List.mem_flatMap.mp hr
  exact fullChart_range_basedOn (EmptyLoops.blockFEmpty_perm x hx) (by decide) r hr

theorem relabelSeven_range12_perm {x : List Nat} (hx : x.Perm (List.range 7)) :
    ((List.range 12).map (relabelSeven x)).Perm (List.range 12) := by
  have hdecomp : List.range 12 = List.range 7 ++ [7,8,9,10,11] := by decide
  rw [hdecomp, List.map_append, relabelSeven_range hx]
  have htail : [7,8,9,10,11].map (relabelSeven x) = [7,8,9,10,11] := by
    simp only [List.map_cons, List.map_nil]
    rw [relabelSeven_fixed x (by decide), relabelSeven_fixed x (by decide),
      relabelSeven_fixed x (by decide), relabelSeven_fixed x (by decide),
      relabelSeven_fixed x (by decide)]
  rw [htail]
  exact hx.append_right _

theorem nativeRows_basedOn : BasedOn (List.range 12) 12 nativeRows := by
  apply basedOn_append (extendRange_basedOn seedRows_basedOn 4 (by decide))
  intro r hr
  obtain ⟨x,hx,hr⟩ := List.mem_flatMap.mp hr
  have hxperm := EmptyLoops.halfarAncestors_perm x hx
  have hmap := basedOn_map localRows_basedOn (relabelSeven x) (relabelSeven_injective hxperm)
  rw [relabelSeven_fixed x (by decide : 7≤12)] at hmap
  exact basedOn_perm_alphabet hmap (relabelSeven_range12_perm hxperm) r hr

end SuperpermutationUpperBound.Native14.Partition
