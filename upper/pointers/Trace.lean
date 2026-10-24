module

public import upper.seed_family.Occurrence

@[expose] public section

/-! A small forward verifier for source-row connector pointers.  The verifier
only visits the selected local paths; its soundness refers to the entire
transported trail. -/
namespace SuperpermutationUpperBound.Native14.Pointers
open CircleTransport Transport SeedFamily

structure Point where
  row : Row Nat
  excess : Int
  deriving DecidableEq

def Point.Occurs (p : Point) (rs : List (Row Nat)) : Prop :=
  RowOccurrence rs p.row p.excess

/-- Prefix excess after transport, before entering the selected local path. -/
def before (h : Nat) (start : Fin (h+1)) (e : Int) : Int :=
  e - ((start.val : Int)-e) / ((h+1 : Nat) : Int)

theorem before_ledger (h : Nat) (start : Fin (h+1)) (e : Int) :
    ((h+1 : Nat) : Int) * before h start e =
      ((h+2 : Nat) : Int)*e + (shiftPort h (-e) start).val-start.val := by
  rw [shiftPort_val]
  have hd := Int.emod_add_mul_ediv ((start.val : Int)-e) ((h+1 : Nat) : Int)
  simp only [before]
  push_cast at *
  rw [show (start.val : Int) + -e = start.val-e by ring]
  have hr : ((start.val : Int)-e) % (h+1) =
      start.val-e-(h+1)*((start.val-e)/(h+1)) := by omega
  rw [hr]
  ring

def liftPoint (h z : Nat) (start : Fin (h+1)) (offset : Nat) (p : Point) : Option Point :=
  let path := Transport.portPath p.row z (shiftPort h (-p.excess) start).val
  path[offset]?.map fun r =>
    ⟨r, before h start p.excess + signedExcess (path.take offset)⟩

theorem liftPoint_sound {rs : List (Row Nat)} {p q : Point}
    (hp : p.Occurs rs) (h z : Nat) (hn : 1≤h) (hs : Shape (h+2) rs)
    (start : Fin (h+1)) (offset : Nat) (hc : liftPoint h z start offset p = some q) :
    q.Occurs (transportWalk rs z start.val) := by
  unfold liftPoint at hc
  dsimp only at hc
  cases he : (Transport.portPath p.row z (shiftPort h (-p.excess) start).val)[offset]? with
  | none =>
    rw [he] at hc
    simp at hc
  | some r =>
    rw [he] at hc
    have hh := List.getElem?_eq_some_iff.mp he
    obtain ⟨hi,hr⟩ := hh
    simp only [Option.map_some, Option.some.injEq] at hc
    subst q
    have ho := RowOccurrence.of_index
      (Transport.portPath p.row z (shiftPort h (-p.excess) start).val) ⟨offset,hi⟩
    simp only [hr] at ho
    exact hp.transport z h hn hs start (shiftPort h (-p.excess) start) rfl ho
      (before_ledger h start p.excess)

def checkIncidence (p : Point) (port : Fin 11) (circle : List Nat) (rotation : Nat) : Bool :=
  decide (13∈circle ∧ rotation<circle.length ∧
    rot circle rotation = insertLetter p.row.head 13 (shiftPort 10 (-p.excess) port).val)

theorem checkIncidence_sound {rs : List (Row Nat)} {p : Point}
    (hp : p.Occurs rs) (hs : Shape 12 rs) (port : Fin 11)
    (circle : List Nat) (rotation : Nat)
    (hc : checkIncidence p port circle rotation = true) :
    SafeIncidence rs 13 port circle := by
  obtain ⟨hf,hr,he⟩ := of_decide_eq_true hc
  exact hp.safeIncidence 13 10 (by omega) hs port circle hf ⟨rotation,hr⟩ he

end SuperpermutationUpperBound.Native14.Pointers
