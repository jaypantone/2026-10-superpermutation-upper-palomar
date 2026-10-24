module

public import SuperpermutationUpperBound.Partition.Basic
public import SuperpermutationUpperBound.Transport.Winding

@[expose] public section

/-! Linear Boolean checks with semantic soundness. Using `List.all` avoids
expanding a decidable bounded quantifier into repeated membership proofs. -/
namespace SuperpermutationUpperBound.Native14.Certificate

/-- Decode the compact ASCII source alphabet 0..9,A,B. -/
def decodeLetter (c : Char) : Nat :=
  if c.toNat ≤ 57 then c.toNat-48 else c.toNat-55

def decodeRow (satellite : Nat) (r : String × Nat) : Row Nat :=
  ⟨r.1.toList.map decodeLetter, satellite, r.2⟩

/-- Fixed-width row decoder. Each block consists of n ordinary symbols and
one F/S visibility marker. The recursion is structural in the character list. -/
def decodePackedRowsAux (n satellite : Nat) : List Char → List Nat → Nat → List (Row Nat)
  | [], _, _ => []
  | c :: cs, rev, i =>
      if i < n then decodePackedRowsAux n satellite cs (decodeLetter c :: rev) (i+1)
      else ⟨rev.reverse, satellite, if c = 'F' then n else n-2⟩ ::
        decodePackedRowsAux n satellite cs [] 0

def decodePackedRows (n satellite : Nat) (s : String) : List (Row Nat) :=
  decodePackedRowsAux n satellite s.toList [] 0

/-- Fixed-width ordinary or connector tuples, without per-row expression trees. -/
def decodePackedBasesAux (n : Nat) : List Char → List Nat → Nat → List (List Nat)
  | [], _, _ => []
  | c :: cs, rev, i =>
      if i+1 = n then (decodeLetter c :: rev).reverse :: decodePackedBasesAux n cs [] 0
      else decodePackedBasesAux n cs (decodeLetter c :: rev) (i+1)

def decodePackedBases (n : Nat) (s : String) : List (List Nat) :=
  decodePackedBasesAux n s.toList [] 0

def basedOnCheck (alphabet : List Nat) (satellite : Nat) (rs : List (Row Nat)) : Bool :=
  rs.all (fun r => decide (r.Valid ∧ r.base.Perm alphabet ∧ r.satellite = satellite ∧
    (r.visible = r.base.length ∨ r.visible = r.base.length-2)))

theorem basedOn_of_check {alphabet : List Nat} {satellite : Nat} {rs : List (Row Nat)}
    (h : basedOnCheck alphabet satellite rs = true) : BasedOn alphabet satellite rs := by
  intro r hr
  exact of_decide_eq_true ((List.all_eq_true.mp h) r hr)

def closedTrailCheck (rs : List (Row Nat)) : Bool :=
  !rs.isEmpty && (rs.zip (rs.rotateLeft 1)).all (fun p => decide (p.1.tail = p.2.head))

theorem closedTrail_of_check {rs : List (Row Nat)}
    (h : closedTrailCheck rs = true) : ClosedTrail rs := by
  have hh := Bool.and_eq_true_iff.mp h
  refine ⟨?_, ?_⟩
  · intro he
    subst rs
    simp at hh
  · intro p hp
    change p.1.tail = p.2.head
    exact of_decide_eq_true ((List.all_eq_true.mp hh.2) p hp)

end SuperpermutationUpperBound.Native14.Certificate
