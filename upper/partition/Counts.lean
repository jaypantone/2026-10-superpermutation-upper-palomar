module

public import upper.partition.Validity
public import upper.partition.ExtensionCounts

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Partition
open SuperpermutationUpperBound.Partition
open Certificate

theorem seedRows_length : seedRows.length = 4704 := by
  simp [seedRows, Halfar0.rows_length, Halfar1.rows_length]

theorem seedRows_charge : (seedRows.map Row.charge).sum = 2352 := by
  simp [seedRows, Halfar0.rows_charge, Halfar1.rows_charge]

theorem blockRows_length : blockRows.length = 4074 := by
  simp [blockRows, BlockF0.rows_length, BlockF1.rows_length, BlockF2.rows_length]

theorem blockRows_charge : (blockRows.map Row.charge).sum = 2058 := by
  simp [blockRows, BlockF0.rows_charge, BlockF1.rows_charge, BlockF2.rows_charge]

theorem localRows_length : localRows.length = 55440 := by
  have hlen := Transport.packingRows_length blockRows 11 11
    (by simpa using blockRows_basedOn.ready (by simp) (by decide : 11≠12))
  have hcharts := flatMap_const_length EmptyLoops.blockFEmpty
    (fun x => fullChart x 11 12) 11 (by
      intro x hx
      rw [fullChart_length]
      exact (EmptyLoops.blockFEmpty_perm x hx).length_eq)
  rw [localRows, List.length_append, hlen, blockRows_length, hcharts,
    EmptyLoops.blockFEmpty_length]

theorem localRows_charge : (localRows.map Row.charge).sum = 22638 := by
  exact append_charge_eq
    (packingRows_charge_eq (z:=11) (n:=11)
      (by simpa using blockRows_basedOn.ready (by simp) (by decide : 11≠12))
      blockRows_charge)
    (fullCharts_charge_zero EmptyLoops.blockFEmpty 11 12)

set_option maxHeartbeats 10000 in
theorem nativeRows_length : nativeRows.length = 39916800 := by
  have houter := extendRange_length seedRows_basedOn 4 (by decide : 8+4≤12)
  have hinner := flatMap_const_length EmptyLoops.halfarAncestors
    (fun x => localRows.map (Row.map (relabelSeven x))) 55440
    (fun _ _ => by simpa using localRows_length)
  rw [nativeRows, List.length_append, houter, seedRows_length, hinner,
    EmptyLoops.halfarAncestors_length]
  decide

private theorem transported_relabelled_charge {α : Type}
    (rs ts : List (Row Nat)) (xs : List α) (f : α → Nat → Nat)
    (n s k p q c : Nat) (hb : BasedOn (List.range n) s rs)
    (hns : n+k≤s) (hp : (rs.map Row.charge).sum=p)
    (hq : (ts.map Row.charge).sum=q) (hc : xs.length=c) :
    (((extendRange rs n k ++ xs.flatMap (fun x => ts.map (Row.map (f x)))).map
      Row.charge).sum) = n.ascFactorial k * p + c * q := by
  have houter := (extendRange_charge hb k hns).trans
    (congrArg (fun a : Nat => n.ascFactorial k * a) hp)
  have hinner := (flatMap_const_charge xs
    (fun x => ts.map (Row.map (f x))) q
    (fun x _ => (mapRows_charge ts (f x)).trans hq)).trans
      (congrArg (fun a : Nat => a*q) hc)
  exact append_charge_eq houter hinner

set_option maxHeartbeats 10000 in
theorem nativeRows_charge : (nativeRows.map Row.charge).sum = 19714464 := by
  have h := transported_relabelled_charge seedRows localRows
    EmptyLoops.halfarAncestors relabelSeven 8 12 4 2352 22638 48
    seedRows_basedOn (by decide) seedRows_charge localRows_charge
    EmptyLoops.halfarAncestors_length
  exact h

end SuperpermutationUpperBound.Native14.Partition
