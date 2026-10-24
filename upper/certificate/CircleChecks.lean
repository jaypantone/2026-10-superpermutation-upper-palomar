module

public import upper.certificate.Checks
public import upper.Iteration

@[expose] public section

/-! Linear checks for the compact native connector-circle data. -/
namespace SuperpermutationUpperBound.Native14.Certificate
open CircleTransport

def decodeCircle (s : String) : List Nat := s.toList.map decodeLetter

def nativeCircleCheck (cs : List (List Nat)) : Bool :=
  cs.all (fun c => decide (c.length = 11 ∧ c.Nodup ∧ 13 ∈ c ∧
    ∀ a ∈ c, a < 14 ∧ a ≠ 12))

/-- Reuse independently checked pieces without decoding the whole family. -/
theorem nativeCircleCheck_append (cs ds : List (List Nat)) :
    nativeCircleCheck (cs ++ ds) = (nativeCircleCheck cs && nativeCircleCheck ds) := by
  simp only [nativeCircleCheck, List.all_append]

theorem nativeCircles_valid_of_check {cs : List (List Nat)}
    (h : nativeCircleCheck cs = true) : CircleFamilyValid 11 cs := by
  intro c hc
  have hh : c.length = 11 ∧ c.Nodup ∧ 13 ∈ c ∧ ∀ a ∈ c, a < 14 ∧ a ≠ 12 :=
    of_decide_eq_true ((List.all_eq_true.mp h) c hc)
  exact ⟨hh.1, hh.2.1⟩

theorem nativeCircles_final_of_check {cs : List (List Nat)}
    (h : nativeCircleCheck cs = true) : ∀ c ∈ cs, 13 ∈ c := by
  intro c hc
  have hh : c.length = 11 ∧ c.Nodup ∧ 13 ∈ c ∧ ∀ a ∈ c, a < 14 ∧ a ≠ 12 :=
    of_decide_eq_true ((List.all_eq_true.mp h) c hc)
  exact hh.2.2.1

theorem nativeCircles_support_of_check {cs : List (List Nat)}
    (h : nativeCircleCheck cs = true) : Iteration.CircleSupport 0 cs := by
  intro c hc
  have hh : c.length = 11 ∧ c.Nodup ∧ 13 ∈ c ∧ ∀ a ∈ c, a < 14 ∧ a ≠ 12 :=
    of_decide_eq_true ((List.all_eq_true.mp h) c hc)
  simpa only [Nat.zero_add] using hh.2.2.2

end SuperpermutationUpperBound.Native14.Certificate
