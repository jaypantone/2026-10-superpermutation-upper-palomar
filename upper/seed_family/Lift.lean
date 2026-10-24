module

public import upper.regularization.RepeatTracks

@[expose] public section

namespace SuperpermutationUpperBound.Native14.SeedFamily
open CircleTransport Transport
variable {α : Type}

theorem finRange_enumeration (xs : List α) :
    (List.finRange xs.length).map (fun i=>xs[i.val])=xs := by
  apply List.ext_getElem (by simp)
  intro j hj hj'
  simp

def Shape (n : Nat) (rs : List (Row α)) : Prop :=
  ∀r∈rs,r.base.length=n ∧ (r.visible=r.base.length ∨ r.visible=r.base.length-2)

def Regular (h : Nat) (families : List (List (Row α))) : Prop :=
  ∀rs∈families, ClosedTrail rs ∧ (h:Int) ∣ signedExcess rs ∧ Shape (h+1) rs

def step (h : Nat) (z : α) (families : List (List (Row α))) : List (List (Row α)) :=
  families.flatMap (fun rs => (List.finRange h).map (fun p => transportWalk rs z p.val))


theorem mem_step {h : Nat} {z : α} {families : List (List (Row α))}
    {t : List (Row α)} (ht : t∈step h z families) :
    ∃rs∈families,∃p:Fin h,t=transportWalk rs z p.val := by
  obtain ⟨rs,hrs,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨p,_,he⟩ := List.mem_map.mp ht
  exact ⟨rs,hrs,p,he.symm⟩

theorem step_length (h : Nat) (z : α) (families : List (List (Row α))) :
    (step h z families).length = h*families.length := by
  induction families with
  | nil => simp [step]
  | cons rs families ih => simp [step, Nat.mul_comm, Nat.mul_add, Nat.add_comm]

theorem transportWalk_shape (n : Nat) (hn : 3≤n) (rs : List (Row α)) (z : α)
    (hs : Shape n rs) (p : Nat) : Shape (n+1) (transportWalk rs z p) := by
  induction rs generalizing p with
  | nil => simp [Shape, transportWalk]
  | cons r rs ih =>
      have hr := hs r (by simp)
      have ht : Shape n rs := fun s h => hs s (by simp [h])
      intro s hm
      rcases List.mem_append.mp hm with hm | hm
      · have hh := transportPath_metadata r z p (by omega) hr.2 s hm
        exact ⟨by omega,hh.2⟩
      · exact ih ht _ s hm

theorem step_regular (h : Nat) (hn : 3≤h+1) (z : α)
    {families : List (List (Row α))} (hr : Regular h families) :
    Regular (h+1) (step h z families) := by
  intro t ht
  obtain ⟨rs,hrs,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp ht
  have hs := hr rs hrs
  have hl : ∀r∈rs,r.base.length=h+1 := fun r hm => (hs.2.2 r hm).1
  have hk := fun r hm => (hs.2.2 r hm).2
  exact ⟨transportWalk_closedTrail hs.1 z h hn hl hk hs.2.1 p.val p.isLt,
    transportWalk_winding_divisible rs z h hn hl hk hs.2.1 p.val p.isLt,
    transportWalk_shape (h+1) hn rs z hs.2.2 p.val⟩

theorem step_inventory (h : Nat) (hn : 3≤h+1) (z : α)
    (families : List (List (Row α)))
    (hl : ∀rs∈families,∀r∈rs,r.base.length=h+1) :
    (step h z families).flatten.Perm (Transport.packingRows families.flatten z) := by
  induction families with
  | nil => simp [step,Transport.packingRows]
  | cons rs families ih =>
      have hs := transportWalk_inventory rs z h hn (hl rs (by simp))
      have ht := ih (fun xs hx => hl xs (by simp [hx]))
      simpa only [step,List.flatMap_cons,List.flatten_append,List.flatten_cons,
        Transport.packingRows,List.flatMap_append,←List.flatMap_def] using hs.append ht

/-- Row occurrence inventory is respected even when its source enumeration changes. -/
theorem packingRows_perm {xs ys : List (Row α)} (hp : xs.Perm ys) (z : α) :
    (Transport.packingRows xs z).Perm (Transport.packingRows ys z) :=
  hp.flatMap_right (fun r => Transport.rows r z)

end SuperpermutationUpperBound.Native14.SeedFamily
