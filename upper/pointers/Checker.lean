module

public import upper.pointers.ConcreteTrace
public import upper.pointers.Index
public import upper.pointers.RangeCheck

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Pointers
open CircleTransport Transport SeedFamily Certificate

def sourceIndex (w : Nat) : Nat := w%4096
def offsetMask (w : Nat) : Nat := w/4096%16
def repeatLap (w : Nat) : Nat := w/65536%8
def circleIndex (w : Nat) : Nat := w/524288%16384
def circleRotation (w : Nat) : Nat := w/8589934592
def completionPort (key : Nat) : Fin 11 := ⟨key%11,Nat.mod_lt _ (by decide)⟩

noncomputable def traceAt (i w : Nat) : Option Point :=
  if i < 10080 then
    outsideTrace (decide (5040 ≤ i)) (p7 i) (p8 i) (p9 i) (p10 i)
      (sourceIndex w) (offsetMask w)
  else (mixedTrace (blockIndex i) (sourceIndex w) (repeatLap w) (offsetMask w%2)).map
    (relabelPoint (ancestor i))

theorem traceAt_sound (i w : Nat) {p : Point} (hc : traceAt i w=some p) :
    p.Occurs (parentAt i) := by
  unfold traceAt at hc
  unfold parentAt
  split_ifs at hc ⊢ with hi
  · exact outsideTrace_sound _ _ _ _ _ _ _ hc
  · obtain ⟨q,hq,hp⟩ := Option.map_eq_some_iff.mp hc
    subst p
    exact relabelPoint_sound _ (mixedTrace_sound _ _ _ _ hq)

theorem parentAt_shape (i : Nat) : Shape 12 (parentAt i) := by
  unfold parentAt
  split
  · exact outsideAt_shape _ _ _ _ _
  · exact shape_relabel _ (mixedAt_shape _)

/-- The decoded source trace must end at an actual vertex of a listed circle.
Each table position specifies its parent and completion port independently of
the witness stored at that position. -/
noncomputable def checkEntry (circles : Nat → List Nat) (key w : Nat) : Bool :=
  decide (circleIndex w < 14774) &&
    (traceAt (key/11) w).any
      (fun p=>checkIncidence p (completionPort key) (circles (circleIndex w)) (circleRotation w))

theorem checkEntry_sound (lookup : Nat → List Nat) (circles : List (List Nat))
    (hm : ∀i<14774,lookup i∈circles) (key w : Nat)
    (hc : checkEntry lookup key w=true) :
    ∃c∈circles, SafeIncidence (parentAt (key/11)) 13 (completionPort key) c := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hi : circleIndex w<14774 := of_decide_eq_true hh.1
  have ht := hh.2
  cases he : traceAt (key/11) w with
  | none => simp only [he,Option.any_none] at ht; contradiction
  | some p =>
      simp only [he,Option.any_some] at ht
      exact ⟨lookup (circleIndex w),hm _ hi,
        checkIncidence_sound (traceAt_sound _ _ he) (parentAt_shape _) _ _ _ ht⟩

end SuperpermutationUpperBound.Native14.Pointers
