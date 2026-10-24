module

public import upper.certificate.Checks
public import SuperpermutationUpperBound.Transport.OrbitAssembly

@[expose] public section

/-! Bounded seed certificates compose actual consecutive paths. Each segment
checks its own last-to-next boundary; the final segment returns to the first row. -/
namespace SuperpermutationUpperBound.Native14.Certificate
open Transport

/-- Check successive row endpoints from an explicit first row. -/
def rowChainCheck (first : Row Nat) : List (Row Nat) → Bool
  | [] => true
  | next :: rest => decide (first.tail = next.head) && rowChainCheck next rest

theorem rowChainCheck_sound {first : Row Nat} {rest : List (Row Nat)}
    (h : rowChainCheck first rest = true) : RowTrailCompatible first rest := by
  induction rest generalizing first with
  | nil => trivial
  | cons next rest ih =>
      have hh := Bool.and_eq_true_iff.mp h
      exact ⟨(of_decide_eq_true hh.1 : first.tail = next.head), ih hh.2⟩

/-- A nonempty segment, including its boundary to an explicit successor row. -/
def pathRunsToCheck (path : List (Row Nat)) (last : Row Nat) : Bool :=
  match path with
  | [] => false
  | first :: rest => rowChainCheck first (rest ++ [last])

theorem pathRunsToCheck_sound {path : List (Row Nat)} {last : Row Nat}
    (h : pathRunsToCheck path last = true) : PathRunsTo path last := by
  cases path with
  | nil => simp [pathRunsToCheck] at h
  | cons first rest => exact rowChainCheck_sound h

theorem basedOnCheck_append (alphabet : List Nat) (satellite : Nat)
    (xs ys : List (Row Nat)) :
    basedOnCheck alphabet satellite (xs ++ ys) =
      (basedOnCheck alphabet satellite xs && basedOnCheck alphabet satellite ys) := by
  simp only [basedOnCheck, List.all_append]

theorem head_append_of_head {α : Type} {xs ys : List α} {first : α}
    (h : xs.head? = some first) : (xs ++ ys).head? = some first := by
  cases xs with
  | nil => simp at h
  | cons x xs => exact h

theorem pathRunsTo_append_of_head {left right : List (Row Nat)} {first last : Row Nat}
    (hhead : right.head? = some first) (hl : PathRunsTo left first)
    (hr : PathRunsTo right last) : PathRunsTo (left ++ right) last := by
  cases right with
  | nil => simp at hhead
  | cons r rest =>
      have heq : r = first := by simpa only [List.head?_cons, Option.some.injEq] using hhead
      subst r
      exact Transport.pathRunsTo_append hl hr

theorem closedTrail_of_head_and_path {rs : List (Row Nat)} {first : Row Nat}
    (hhead : rs.head? = some first) (hpath : PathRunsTo rs first) : ClosedTrail rs := by
  cases rs with
  | nil => simp at hhead
  | cons r rest =>
      have heq : r = first := by simpa only [List.head?_cons, Option.some.injEq] using hhead
      subst r
      exact Transport.closedTrail_of_pathRunsTo hpath

end SuperpermutationUpperBound.Native14.Certificate
