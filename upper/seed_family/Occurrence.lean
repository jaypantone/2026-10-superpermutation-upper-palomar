module

public import upper.seed_family.Lift
public import upper.seed_family.Relabel
public import upper.review.SparsePointers

@[expose] public section

namespace SuperpermutationUpperBound.Native14.SeedFamily
open CircleTransport Transport
open ImprovedUpper.Review
variable {α β : Type}

/-- An actual occurrence, retaining the signed ledger before that occurrence. -/
def RowOccurrence (rs : List (Row α)) (r : Row α) (excess : Int) : Prop :=
  ∃pre post,rs=pre++r::post ∧ signedExcess pre=excess

theorem Shape.repeatRows {n : Nat} {rs : List (Row α)} (hs : Shape n rs) (k : Nat) :
    Shape n (Regularization.repeatRows rs k) :=
  fun r hr=>hs r (Regularization.repeatRows_mem hr)

namespace RowOccurrence

theorem of_index (rs : List (Row α)) (i : Fin rs.length) :
    RowOccurrence rs rs[i.val] (signedExcess (rs.take i.val)) := by
  refine ⟨rs.take i.val,rs.drop (i.val+1),?_,rfl⟩
  rw [←List.drop_eq_getElem_cons i.isLt,List.take_append_drop]

theorem mem {rs : List (Row α)} {r : Row α} {e : Int}
    (ho : RowOccurrence rs r e) : r∈rs := by
  obtain ⟨pre,post,rfl,_⟩ := ho
  simp

theorem map (f : α→β) {rs : List (Row α)} {r : Row α} {e : Int}
    (ho : RowOccurrence rs r e) : RowOccurrence (rs.map (Row.map f)) (r.map f) e := by
  obtain ⟨pre,post,rfl,he⟩ := ho
  refine ⟨pre.map (Row.map f),post.map (Row.map f),?_,?_⟩
  · simp only [List.map_append,List.map_cons]
  · simpa only [signedExcess_map] using he

theorem append_right {rs : List (Row α)} {r : Row α} {e : Int}
    (ho : RowOccurrence rs r e) (tail : List (Row α)) : RowOccurrence (rs++tail) r e := by
  obtain ⟨pre,post,rfl,he⟩ := ho
  exact ⟨pre,post++tail,by simp only [List.append_assoc,List.cons_append],he⟩

theorem append_left (initial : List (Row α)) {rs : List (Row α)} {r : Row α} {e : Int}
    (ho : RowOccurrence rs r e) : RowOccurrence (initial++rs) r (signedExcess initial+e) := by
  obtain ⟨pre,post,rfl,he⟩ := ho
  exact ⟨initial++pre,post,by simp only [List.append_assoc],by rw [signedExcess_append,he]⟩

theorem repeat_lap {rs : List (Row α)} {r : Row α} {e : Int}
    (ho : RowOccurrence rs r e) (n lap : Nat) (hlap : lap<n) :
    RowOccurrence (Regularization.repeatRows rs n) r ((lap:Int)*signedExcess rs+e) := by
  induction n generalizing lap with
  | zero => omega
  | succ n ih =>
      cases lap with
      | zero => simpa only [Regularization.repeatRows,Nat.cast_zero,zero_mul,zero_add]
          using ho.append_right (Regularization.repeatRows rs n)
      | succ lap =>
          have hh := (ih lap (by omega)).append_left rs
          have he : signedExcess rs+((lap:Int)*signedExcess rs+e)=
              ((lap+1:Nat):Int)*signedExcess rs+e := by push_cast;ring
          simpa only [Regularization.repeatRows,he] using hh

/-- Semantic transport of an occurrence. The only numerical inputs are the
checked modular port and the checked integer prefix ledger. The local path
contains at most two rows in the full/short construction. -/
theorem transport {rs : List (Row α)} {r s : Row α} {e localE nextE : Int}
    (ho : RowOccurrence rs r e) (z : α) (h : Nat) (hn : 1≤h)
    (hs : Shape (h+2) rs) (start port : Fin (h+1))
    (hp : shiftPort h (-e) start=port)
    (hl : RowOccurrence (Transport.portPath r z port.val) s localE)
    (hc : ((h+1:Nat):Int)*nextE = ((h+2:Nat):Int)*e + port.val-start.val) :
    RowOccurrence (transportWalk rs z start.val) s (nextE+localE) := by
  obtain ⟨pre,post,hdecomp,he⟩ := ho
  have hpre : ∀a∈pre,a∈rs := by
    intro a ha
    rw [hdecomp]
    exact List.mem_append_left _ ha
  have hlen : ∀a∈pre,a.base.length=h+2 := fun a ha=>(hs a (hpre a ha)).1
  have hkind := fun a ha=>(hs a (hpre a ha)).2
  have hexit : completionExit pre start.val=port.val := by
    rw [completionExit_eq_shift pre h (by omega) hlen hkind start]
    have hd : (pre.map delta).sum = -e := by
      have hd := signedExcess_eq_neg_sum_delta pre
      rw [he] at hd
      omega
    rw [hd,hp]
  have hledger : signedExcess (transportWalk pre z start.val)=nextE := by
    exact transport_prefix_excess_of_ledger pre z (h+1) (by omega) hlen hkind
      start.val start.isLt e nextE port.val he hexit hc
  obtain ⟨localPre,localPost,hlocal,hlocalE⟩ := hl
  refine ⟨transportWalk pre z start.val++localPre,
    localPost++transportWalk post z (portTarget r port.val),?_,?_⟩
  · rw [hdecomp,Regularization.transportWalk_append,hexit,transportWalk,hlocal]
    simp only [List.append_assoc,List.cons_append]
  · rw [signedExcess_append,hledger,hlocalE]

/-- An occurrence ledger suffices for a semantic connector witness. -/
theorem safeIncidence {rs : List (Row α)} {r : Row α} {e : Int}
    (ho : RowOccurrence rs r e) (final : α) (h : Nat) (hn : 1≤h)
    (hs : Shape (h+2) rs) (j : Fin (h+1)) (circle : List α)
    (hfinal : final∈circle) (rotation : Fin circle.length)
    (hv : rot circle rotation.val=insertLetter r.head final (shiftPort h (-e) j).val) :
    SafeIncidence rs final j circle := by
  obtain ⟨pre,post,hd,he⟩ := ho
  exact safeIncidence_of_prefix_excess rs final h hn j circle
    (fun a ha=>(hs a ha).1) (fun a ha=>(hs a ha).2)
    pre r post hd e he hfinal rotation hv

end RowOccurrence
end SuperpermutationUpperBound.Native14.SeedFamily
