module

public import upper.pointers.Trace

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Pointers

/-- A table is read in order. Each entry must certify its own index. -/
def rangeCheck (check : Nat → Nat → Bool) : Nat → List Nat → Bool
  | _, [] => true
  | start, x::xs => check start x && rangeCheck check (start+1) xs

theorem rangeCheck_append (check : Nat → Nat → Bool) (start : Nat)
    (xs ys : List Nat) :
    rangeCheck check start (xs++ys) =
      (rangeCheck check start xs && rangeCheck check (start+xs.length) ys) := by
  induction xs generalizing start with
  | nil => simp [rangeCheck]
  | cons x xs ih =>
      simp only [List.cons_append,rangeCheck,ih,List.length_cons]
      rw [show start+1+xs.length=start+(xs.length+1) by omega]
      exact Bool.and_assoc _ _ _ |>.symm

theorem rangeCheck_sound {check : Nat → Nat → Bool} {start : Nat} {xs : List Nat}
    (hc : rangeCheck check start xs = true) (i : Nat) (hi : i<xs.length) :
    ∃w, check (start+i) w = true := by
  induction xs generalizing start i with
  | nil => simp at hi
  | cons x xs ih =>
      have hh := Bool.and_eq_true_iff.mp hc
      cases i with
      | zero => exact ⟨x,by simpa using hh.1⟩
      | succ i =>
          have hh' := ih hh.2 i (by simpa using hi)
          simpa only [Nat.add_assoc,Nat.add_comm 1 i] using hh'

end SuperpermutationUpperBound.Native14.Pointers
