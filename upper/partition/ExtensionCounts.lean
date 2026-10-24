module

public import upper.partition.Extension
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Partition

theorem extendRange_length {rs : List (Row Nat)} {n s : Nat}
    (hb : BasedOn (List.range n) s rs) (k : Nat) (hns : n+k ≤ s) :
    (extendRange rs n k).length = n.ascFactorial k * rs.length := by
  induction k with
  | zero => simp [extendRange]
  | succ k ih =>
      have hr := extendRange_basedOn hb k (by omega)
      have hcount := Transport.packingRows_length (extendRange rs n k) (n+k) (n+k)
        (by simpa using hr.ready (by simp) (by omega))
      rw [extendRange, hcount, ih (by omega), Nat.ascFactorial_succ]
      simp [Nat.mul_assoc, Nat.add_mul, Nat.add_comm]

theorem extendRange_charge {rs : List (Row Nat)} {n s : Nat}
    (hb : BasedOn (List.range n) s rs) (k : Nat) (hns : n+k ≤ s) :
    ((extendRange rs n k).map Row.charge).sum =
      n.ascFactorial k * (rs.map Row.charge).sum := by
  induction k with
  | zero => simp [extendRange]
  | succ k ih =>
      have hr := extendRange_basedOn hb k (by omega)
      have hcount := Transport.packingRows_charge_sum (extendRange rs n k) (n+k) (n+k)
        (by simpa using hr.ready (by simp) (by omega))
      rw [extendRange, hcount, ih (by omega), Nat.ascFactorial_succ]
      simp [Nat.mul_assoc, Nat.add_mul, Nat.add_comm]

theorem flatMap_const_length {α β : Type} (xs : List α) (f : α → List β) (n : Nat)
    (hf : ∀ x∈xs, (f x).length=n) : (xs.flatMap f).length = xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.flatMap_cons, List.length_append, hf x (by simp),
        ih (fun x hx => hf x (List.mem_cons_of_mem _ hx)), List.length_cons]
      simp [Nat.mul_assoc, Nat.add_mul, Nat.add_comm]

theorem flatMap_const_charge {α : Type} (xs : List α) (f : α → List (Row Nat)) (q : Nat)
    (hf : ∀ x∈xs, ((f x).map Row.charge).sum=q) :
    ((xs.flatMap f).map Row.charge).sum = xs.length*q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, hf x (by simp),
        ih (fun x hx => hf x (List.mem_cons_of_mem _ hx)), List.length_cons]
      simp [Nat.mul_assoc, Nat.add_mul, Nat.add_comm]

theorem mapRows_charge (rs : List (Row Nat)) (f : Nat → Nat) :
    ((rs.map (Row.map f)).map Row.charge).sum = (rs.map Row.charge).sum := by
  simp only [List.map_map, Function.comp_def, Row.map_charge]


theorem packingRows_charge_eq {rs : List (Row Nat)} {z n q : Nat}
    (hr : ∀ r ∈ rs, Transport.Ready z r ∧ r.base.length=n)
    (hq : (rs.map Row.charge).sum=q) :
    ((Transport.packingRows rs z).map Row.charge).sum=n*q := by
  rw [Transport.packingRows_charge_sum rs z n hr, hq]

theorem fullCharts_charge_zero (xs : List (List Nat)) (z s : Nat) :
    ((xs.flatMap (fun x => SuperpermutationUpperBound.Partition.fullChart x z s)).map Row.charge).sum=0 := by
  rw [flatMap_const_charge xs _ 0 (fun _ _ => SuperpermutationUpperBound.Partition.fullChart_charge_sum _ _ _), Nat.mul_zero]

theorem append_charge_eq {rs ts : List (Row Nat)} {p q : Nat}
    (hr : (rs.map Row.charge).sum=p) (ht : (ts.map Row.charge).sum=q) :
    ((rs++ts).map Row.charge).sum=p+q := by
  rw [List.map_append, List.sum_append, hr, ht]

end SuperpermutationUpperBound.Native14.Partition
