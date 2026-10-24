module

public import upper.pointers.FastHalfar0
public import upper.pointers.FastHalfar1
public import upper.pointers.FastBlockF0
public import upper.pointers.FastBlockF1
public import upper.pointers.FastBlockF2
public import upper.seed_family.Membership

@[expose] public section

/-! Logarithmic source-point lookup with proved actual source occurrences. -/
namespace SuperpermutationUpperBound.Native14.Pointers
open Certificate SeedFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

noncomputable def fastOutsidePoint (b : Bool) (i : Nat) : Option Point :=
  match b with
  | false => FastHalfar0.point i
  | true => FastHalfar1.point i

noncomputable def fastF0Point (i : Nat) : Option Point := FastBlockF0.point i
noncomputable def fastF1Point (i : Nat) : Option Point := FastBlockF1.point i
noncomputable def fastF2Point (i : Nat) : Option Point := FastBlockF2.point i

def switchRows (rows0 rows1 : List (Row Nat)) : Bool → List (Row Nat)
  | false => rows0
  | true => rows1

/-- Abstract Boolean selection avoids kernel conversion of concrete trees
while checking the soundness wrapper. -/
theorem switchPoint_sound (rows0 rows1 : List (Row Nat))
    (get0 get1 : Nat → Option Point)
    (h0 : ∀ i {p}, get0 i = some p → p.Occurs rows0)
    (h1 : ∀ i {p}, get1 i = some p → p.Occurs rows1)
    (b : Bool) (i : Nat) {p : Point}
    (hp : (match b with | false => get0 i | true => get1 i) = some p) :
    p.Occurs (switchRows rows0 rows1 b) := by
  cases b with
  | false => exact h0 i hp
  | true => exact h1 i hp

theorem fastOutsidePoint_sound (b : Bool) (i : Nat) {p : Point}
    (hp : fastOutsidePoint b i = some p) : p.Occurs (outsideSource b) :=
  switchPoint_sound Halfar0.rows Halfar1.rows FastHalfar0.point FastHalfar1.point
    FastHalfar0.point_sound FastHalfar1.point_sound b i hp

theorem fastF0Point_sound (i : Nat) {p : Point} (hp : fastF0Point i = some p) :
    p.Occurs BlockF0.rows := FastBlockF0.point_sound i hp

theorem fastF1Point_sound (i : Nat) {p : Point} (hp : fastF1Point i = some p) :
    p.Occurs BlockF1.rows := FastBlockF1.point_sound i hp

theorem fastF2Point_sound (i : Nat) {p : Point} (hp : fastF2Point i = some p) :
    p.Occurs BlockF2.rows := FastBlockF2.point_sound i hp

#print axioms fastOutsidePoint_sound
#print axioms fastF0Point_sound
#print axioms fastF1Point_sound
#print axioms fastF2Point_sound

end SuperpermutationUpperBound.Native14.Pointers
