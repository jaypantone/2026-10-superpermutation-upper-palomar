module

public import upper.regularization.RepeatTracks

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Regularization
open CircleTransport Transport
variable {α : Type}

/-- A source excess of 126 advances a ten-port lap by four. -/
theorem completionExit_126 (rs : List (Row α))
    (hlen : ∀r∈rs,r.base.length=11)
    (hkind : ∀r∈rs,r.visible=r.base.length ∨ r.visible=r.base.length-2)
    (hex : signedExcess rs=126) (p : Nat) (hp : p<10) :
    completionExit rs p = (p+4)%10 := by
  have hd : (rs.map delta).sum = -126 := by
    have hh := signedExcess_eq_neg_sum_delta rs
    rw [hex] at hh
    omega
  rw [completionExit_eq_shift rs 9 (by decide) hlen hkind ⟨p,hp⟩, hd]
  dsimp [shiftPort]
  omega

/-- The two literal tracks following the even and odd port orbits. -/
def fiveTracks (rs : List (Row α)) (z : α) : List (List (Row α)) :=
  [transportWalk (repeatRows rs 5) z 0, transportWalk (repeatRows rs 5) z 1]

@[simp] theorem fiveTracks_length (rs : List (Row α)) (z : α) :
    (fiveTracks rs z).length = 2 := rfl

/-- Five laps on each of two ports use all ten original single-lap tracks
exactly once. This is an occurrence permutation, with no deduplication. -/
theorem fiveTracks_inventory (rs : List (Row α)) (z : α)
    (hlen : ∀r∈rs,r.base.length=11)
    (hkind : ∀r∈rs,r.visible=r.base.length ∨ r.visible=r.base.length-2)
    (hex : signedExcess rs=126) :
    (fiveTracks rs z).flatten.Perm (Transport.packingRows rs z) := by
  have h0 := completionExit_126 rs hlen hkind hex 0 (by decide)
  have h1 := completionExit_126 rs hlen hkind hex 1 (by decide)
  have h2 := completionExit_126 rs hlen hkind hex 2 (by decide)
  have h3 := completionExit_126 rs hlen hkind hex 3 (by decide)
  have h4 := completionExit_126 rs hlen hkind hex 4 (by decide)
  have h5 := completionExit_126 rs hlen hkind hex 5 (by decide)
  have h6 := completionExit_126 rs hlen hkind hex 6 (by decide)
  have h7 := completionExit_126 rs hlen hkind hex 7 (by decide)
  have h8 := completionExit_126 rs hlen hkind hex 8 (by decide)
  have h9 := completionExit_126 rs hlen hkind hex 9 (by decide)
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have ho : orbitLabels (completionExit rs) 0 5 ++ orbitLabels (completionExit rs) 1 5 =
      [0,4,8,2,6,1,5,9,3,7] := by
    simp only [orbitLabels, h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
    rfl
  have hp : ([0,4,8,2,6,1,5,9,3,7]:List Nat).Perm (List.range 10) := by decide
  simp only [fiveTracks, List.flatten_cons, List.flatten_nil, List.append_nil,
    transportWalk_repeat, orbitRows]
  rw [←List.flatMap_append, ho]
  exact (hp.flatMap_right (transportWalk rs z)).trans
    (transportWalk_range_inventory rs z 10 (by decide) hlen)

/-- Both orbit tracks are genuine closed trails and are regular for the next
transport step. The repeated source list is allowed to have repeated rows;
the inventory theorem separately proves that the output uses each source
replacement occurrence only once. -/
theorem fiveTracks_closed_regular {rs : List (Row α)} (hc : ClosedTrail rs) (z : α)
    (hlen : ∀r∈rs,r.base.length=11)
    (hkind : ∀r∈rs,r.visible=r.base.length ∨ r.visible=r.base.length-2)
    (hex : signedExcess rs=126) :
    ∀t∈fiveTracks rs z, ClosedTrail t ∧ (11:Int) ∣ signedExcess t := by
  have hb : ∀r∈repeatRows rs 5,r.base.length=10+1 :=
    fun r hr => hlen r (repeatRows_mem hr)
  have hk : ∀r∈repeatRows rs 5,r.visible=r.base.length ∨ r.visible=r.base.length-2 :=
    fun r hr => hkind r (repeatRows_mem hr)
  have hw : (10:Int) ∣ signedExcess (repeatRows rs 5) := by
    rw [repeatRows_excess,hex]
    decide
  intro t ht
  have ht' : t=transportWalk (repeatRows rs 5) z 0 ∨
      t=transportWalk (repeatRows rs 5) z 1 := by simpa only [fiveTracks,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using ht
  rcases ht' with rfl | rfl
  all_goals exact ⟨transportWalk_closedTrail (repeatRows_closed hc 5 (by decide)) z 10
      (by decide) hb hk hw _ (by decide),
    transportWalk_winding_divisible (repeatRows rs 5) z 10 (by decide) hb hk hw _ (by decide)⟩

theorem fiveTracks_nodup {rs : List (Row α)} (z : α)
    (hlen : ∀r∈rs,r.base.length=11)
    (hkind : ∀r∈rs,r.visible=r.base.length ∨ r.visible=r.base.length-2)
    (hex : signedExcess rs=126)
    (hnodup : (Transport.packingRows rs z).Nodup) :
    (fiveTracks rs z).flatten.Nodup :=
  (fiveTracks_inventory rs z hlen hkind hex).nodup_iff.mpr hnodup

end SuperpermutationUpperBound.Native14.Regularization
