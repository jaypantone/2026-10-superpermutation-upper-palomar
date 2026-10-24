module

public import upper.partition.Blocks

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Partition

def mergeBlocks : Nat → List (List Nat) → List (List Nat) → List (List Nat)
  | 0, xs, ys => xs++ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | k+1, x::xs, y::ys =>
      if compare x y != Ordering.gt then x::mergeBlocks k xs (y::ys)
      else y::mergeBlocks k (x::xs) ys

theorem mem_mergeBlocks (k : Nat) (xs ys : List (List Nat)) (a : List Nat) :
    a∈mergeBlocks k xs ys ↔ a∈xs ∨ a∈ys := by
  induction k generalizing xs ys with
  | zero => simp [mergeBlocks]
  | succ k ih =>
    cases xs with
    | nil => simp [mergeBlocks]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeBlocks]
      | cons y ys =>
        simp only [mergeBlocks]
        split <;> simp [ih, or_assoc, or_left_comm, or_comm]

def sortBlocks : Nat → List (List Nat) → List (List Nat)
  | 0, xs => xs
  | k+1, xs => mergeBlocks xs.length
      (sortBlocks k (xs.take (xs.length/2))) (sortBlocks k (xs.drop (xs.length/2)))

theorem mem_sortBlocks (k : Nat) (xs : List (List Nat)) (a : List Nat) :
    a∈sortBlocks k xs ↔ a∈xs := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih =>
    rw [sortBlocks, mem_mergeBlocks, ih, ih, ← List.mem_append, List.take_append_drop]

end SuperpermutationUpperBound.Native14.Partition
