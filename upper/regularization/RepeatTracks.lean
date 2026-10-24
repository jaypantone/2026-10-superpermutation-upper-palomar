module

public import SuperpermutationUpperBound.CircleTransport.TrackCounts

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Regularization
open CircleTransport Transport
variable {α : Type}

/-- Literal repetition; the repeated source rows are not asserted distinct. -/
def repeatRows (rs : List (Row α)) : Nat → List (Row α)
  | 0 => []
  | k+1 => rs ++ repeatRows rs k

theorem repeatRows_mem {rs : List (Row α)} {k : Nat} {r : Row α}
    (hr : r ∈ repeatRows rs k) : r ∈ rs := by
  induction k with
  | zero => simp [repeatRows] at hr
  | succ k ih =>
      rcases List.mem_append.mp hr with h | h
      · exact h
      · exact ih h

theorem repeatRows_excess (rs : List (Row α)) (k : Nat) :
    signedExcess (repeatRows rs k) = (k:Int)*signedExcess rs := by
  induction k with
  | zero => simp [repeatRows, signedExcess]
  | succ k ih =>
      have ha (xs ys : List (Row α)) :
          signedExcess (xs++ys)=signedExcess xs+signedExcess ys := by
        simp [signedExcess, List.length_append, List.map_append, List.sum_append]
        omega
      rw [repeatRows, ha, ih]
      push_cast
      ring

theorem repeatRows_closed {rs : List (Row α)} (hc : ClosedTrail rs)
    (k : Nat) (hk : 0<k) : ClosedTrail (repeatRows rs k) := by
  have hi : RowTrailCompatible (rs.head hc.1) rs.tail := by
    cases rs with
    | nil => exact False.elim (hc.1 rfl)
    | cons r rs => exact closedTrail_internal hc
  have heq (j : Nat) : orbitRows (fun _ : Unit => rs) id () j = repeatRows rs j := by
    induction j with
    | zero => rfl
    | succ j ih => simp only [orbitRows_succ, id_eq, ih, repeatRows]
  have hret : advance (id : Unit→Unit) () k = () := by
    induction k with
    | zero => rfl
    | succ k ih => simpa only [advance, id_eq] using ih
  rw [←heq]
  exact orbitRows_closedTrail_of_endpoints (fun _ : Unit => rs) id
    (fun _ => hc.1) (fun _ => hi) (fun _ => closedTrail_last_compatible_head hc) () hk hret

theorem transportWalk_append (xs ys : List (Row α)) (z : α) (p : Nat) :
    transportWalk (xs++ys) z p = transportWalk xs z p ++
      transportWalk ys z (completionExit xs p) := by
  induction xs generalizing p with
  | nil => rfl
  | cons r xs ih =>
      simp only [List.cons_append, transportWalk, completionExit, ih, List.append_assoc]

/-- Repeated source laps become single-lap tracks at the successive exit ports. -/
theorem transportWalk_repeat (rs : List (Row α)) (z : α) (p k : Nat) :
    transportWalk (repeatRows rs k) z p =
      orbitRows (fun q => transportWalk rs z q) (completionExit rs) p k := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => rw [repeatRows, transportWalk_append, ih, orbitRows_succ]

/-- All-label inventory without changing from natural ports to `Fin` labels. -/
theorem transportWalk_range_inventory (rs : List (Row α)) (z : α) (h : Nat)
    (hn : 3≤h+1) (hlen : ∀r∈rs,r.base.length=h+1) :
    ((List.range h).flatMap (transportWalk rs z)).Perm (Transport.packingRows rs z) := by
  have hh := transportWalk_inventory rs z h hn hlen
  rw [←map_val_finRange h, List.flatMap_map]
  exact hh

end SuperpermutationUpperBound.Native14.Regularization
