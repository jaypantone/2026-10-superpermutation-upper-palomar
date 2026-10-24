module

public import SuperpermutationUpperBound.CircleTransport.TrackCounts

@[expose] public section

/-!
A sparse connector witness needs only a parent row occurrence and the signed
prefix ledger. It does not enumerate the completed slices or cyclic classes.
The ledger equality remains an explicit proof obligation: a generated number
alone is not accepted as a proof.
-/
namespace SuperpermutationUpperBound.ImprovedUpper.Review
open Transport CircleTransport

/-- A row occurrence and a checked signed-prefix ledger give semantic connector
incidence. The circle equality concerns only one short endpoint tuple. -/
theorem safeIncidence_of_prefix_excess {α : Type}
    (rs : List (Row α)) (final : α) (h : Nat) (hn : 1 ≤ h)
    (j : Fin (h+1)) (circle : List α)
    (hlen : ∀ r ∈ rs, r.base.length = h+2)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length-2)
    (pre : List (Row α)) (r : Row α) (post : List (Row α))
    (hdecomp : rs = pre ++ r :: post) (excess : Int)
    (hledger : signedExcess pre = excess)
    (hfinal : final ∈ circle) (rotation : Fin circle.length)
    (hvertex : rot circle rotation.val =
      insertLetter r.head final (shiftPort h (-excess) j).val) :
    SafeIncidence rs final j circle := by
  have hpre : ∀ a ∈ pre, a ∈ rs := by
    intro a ha
    rw [hdecomp]
    exact List.mem_append_left _ ha
  have hshift : oldWalkPerm (h+1) (by omega) pre j = shiftPort h (-excess) j := by
    rw [oldWalkPerm_eq_shift pre h (fun a ha => hlen a (hpre a ha))
      (fun a ha => hkind a (hpre a ha))]
    have he := signedExcess_eq_neg_sum_delta pre
    rw [hledger] at he
    have hs : (pre.map delta).sum = -excess := by omega
    rw [hs]
  have hb : BoundaryVertex rs final (h+1) (by omega) j
      (insertLetter r.head final (shiftPort h (-excess) j).val) := by
    exact ⟨pre, r, post, hdecomp, by rw [hshift]⟩
  refine Or.inl ⟨hfinal, _, hb.mem_completionWalk (by omega) hlen hkind, ?_⟩
  exact ⟨rotation, hvertex⟩

/-- Prefix ledgers compose arithmetically, supporting balanced-tree or shared
subexpression proofs for transported parent walks. -/
theorem signedExcess_append (xs ys : List (Row α)) :
    signedExcess (xs ++ ys) = signedExcess xs + signedExcess ys := by
  simp only [signedExcess, List.length_append, List.map_append, List.sum_append,
    Nat.cast_add]
  omega

/-- Repeated copies of a walk need only one signed ledger. -/
theorem signedExcess_flatten_replicate (rs : List (Row α)) (n : Nat) :
    signedExcess (List.replicate n rs).flatten = (n : Int) * signedExcess rs := by
  induction n with
  | zero => simp [signedExcess]
  | succ n ih =>
      simp only [List.replicate_succ, List.flatten_cons, signedExcess_append, ih,
        Nat.cast_add, Nat.cast_one]
      ring

/-- The generic winding ledger also applies to a proper prefix. No closedness
or winding-divisibility assumption is needed. -/
theorem transport_prefix_excess_mul (pre : List (Row α)) (newOrd : α) (h : Nat)
    (hn : 3 ≤ h+1) (hlen : ∀ r ∈ pre, r.base.length = h+1)
    (hkind : ∀ r ∈ pre, r.visible = r.base.length ∨ r.visible = r.base.length-2)
    (p : Nat) (hp : p<h) :
    (h:Int) * signedExcess (transportWalk pre newOrd p) =
      ((h+1:Nat):Int) * signedExcess pre + (completionExit pre p:Int) - (p:Int) := by
  have he := transportWalk_winding_ledger pre newOrd h hn hlen hkind p hp
  rw [signedExcess_eq_neg_sum_delta, signedExcess_eq_neg_sum_delta]
  calc
    (h:Int) * -((transportWalk pre newOrd p).map delta).sum =
        -((h:Int) * ((transportWalk pre newOrd p).map delta).sum) := by ring
    _ = -(((h+1:Nat):Int) * (pre.map delta).sum -
        ((completionExit pre p:Int) - (p:Int))) := congrArg Neg.neg he
    _ = _ := by ring

/-- Small integer arithmetic plus the previous cached prefix ledger certifies
the next prefix ledger; generated numbers alone are never trusted. -/
theorem transport_prefix_excess_of_ledger (pre : List (Row α)) (newOrd : α) (h : Nat)
    (hn : 3 ≤ h+1) (hlen : ∀ r ∈ pre, r.base.length = h+1)
    (hkind : ∀ r ∈ pre, r.visible = r.base.length ∨ r.visible = r.base.length-2)
    (p : Nat) (hp : p<h) (oldExcess newExcess : Int) (exitPort : Nat)
    (hold : signedExcess pre = oldExcess) (hexit : completionExit pre p = exitPort)
    (hcheck : (h:Int)*newExcess = ((h+1:Nat):Int)*oldExcess + exitPort - p) :
    signedExcess (transportWalk pre newOrd p) = newExcess := by
  have he := transport_prefix_excess_mul pre newOrd h hn hlen hkind p hp
  rw [hold, hexit, ← hcheck] at he
  exact mul_left_cancel₀ (by omega : (h:Int) ≠ 0) he

end SuperpermutationUpperBound.ImprovedUpper.Review
