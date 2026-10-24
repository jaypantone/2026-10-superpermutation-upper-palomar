module

public import upper.certificate.CircleChecks

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Pointers

/-- Keep circle encodings opaque while proving the lookup representation.
Only the one circle returned by a lookup is decoded during an incidence check. -/
inductive EncodedCircleTree where
  | leaf (circle : String)
  | branch (leftSize : Nat) (left right : EncodedCircleTree)

namespace EncodedCircleTree

def flatten : EncodedCircleTree → List String
  | .leaf c => [c]
  | .branch _ left right => left.flatten ++ right.flatten

def get : EncodedCircleTree → Nat → String
  | .leaf c, _ => c
  | .branch size left right, i =>
      if i < size then left.get i else right.get (i-size)

/-- Cached sizes affect efficiency only. Every return value is an actual leaf. -/
theorem get_mem (tree : EncodedCircleTree) (i : Nat) : tree.get i ∈ tree.flatten := by
  induction tree generalizing i with
  | leaf c => simp [get, flatten]
  | branch size left right ihl ihr =>
      simp only [get]
      split
      · exact List.mem_append_left _ (ihl i)
      · exact List.mem_append_right _ (ihr (i-size))

theorem decode_get_mem (tree : EncodedCircleTree) (i : Nat) :
    Certificate.decodeCircle (tree.get i) ∈ tree.flatten.map Certificate.decodeCircle :=
  List.mem_map.mpr ⟨tree.get i, tree.get_mem i, rfl⟩

end EncodedCircleTree
end SuperpermutationUpperBound.Native14.Pointers
