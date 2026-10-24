module

public import SuperpermutationUpperBound.CircleTransport.TrackCounts

@[expose] public section

/-! Native n14 iteration; adapted from Pantone's Iterated library. -/
namespace SuperpermutationUpperBound.Native14.Iteration
open Transport CircleTransport
variable {I0 : Type}

/-- Source component occurrences, with one additional port label at each stage. -/
def Index (I0 : Type) : Nat → Type
  | 0 => I0
  | k + 1 => Index I0 k × Fin (k + 11)

instance indexFintype (I0 : Type) [Fintype I0] : (k : Nat) → Fintype (Index I0 k)
  | 0 => by change Fintype I0; infer_instance
  | k + 1 => by
    letI : Fintype (Index I0 k) := indexFintype I0 k
    change Fintype (Index I0 k × Fin (k + 11))
    infer_instance

instance indexDecidableEq (I0 : Type) [DecidableEq I0] : (k : Nat) → DecidableEq (Index I0 k)
  | 0 => by change DecidableEq I0; infer_instance
  | k + 1 => by
    letI : DecidableEq (Index I0 k) := indexDecidableEq I0 k
    change DecidableEq (Index I0 k × Fin (k + 11))
    infer_instance

/-- The enumeration order is explicit and agrees with the finite certificate's
base label list. No set conversion discards repeated row values. -/
def labels (baseLabels : List I0) : (k : Nat) → List (Index I0 k)
  | 0 => baseLabels
  | k + 1 => (labels baseLabels k).product (List.finRange (k + 11))

def family (baseFamily : I0 → List (Row Nat)) : (k : Nat) → Index I0 k → List (Row Nat)
  | 0, i => baseFamily i
  | k + 1, ip => transportWalk (family baseFamily k ip.1) (k + 14) ip.2.val

def circles (baseCircles : List (List Nat)) : Nat → List (List Nat)
  | 0 => baseCircles
  | k + 1 => extendCircles (circles baseCircles k) (k + 14)

/-- The recurrence can be instantiated with377 without importing numerical bounds. -/
def circleCount (c0 : Nat) : Nat → Nat
  | 0 => c0
  | k + 1 => (k + 11) * circleCount c0 k

def CircleSupport (k : Nat) (cs : List (List Nat)) : Prop :=
  ∀ c ∈ cs, ∀ a ∈ c, a < k + 14 ∧ a ≠ 12

theorem labels_complete (baseLabels : List I0) (hb : ∀ i, i ∈ baseLabels) (k : Nat) :
    ∀ i, i ∈ labels baseLabels k := by
  induction k with
  | zero => exact hb
  | succ k ih =>
    intro ⟨i, p⟩
    exact List.mem_product.mpr ⟨ih i, List.mem_finRange p⟩

theorem labels_nodup {baseLabels : List I0} (hb : baseLabels.Nodup) (k : Nat) :
    (labels baseLabels k).Nodup := by
  induction k with
  | zero => exact hb
  | succ k ih => exact ih.product (nodup_finRange _)

/-- Circle representatives use only the available word alphabet and exclude the satellite. -/
theorem circles_support (baseCircles : List (List Nat)) (hs : CircleSupport 0 baseCircles) (k : Nat) :
    CircleSupport k (circles baseCircles k) := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    intro c hc a ha
    obtain ⟨old, hold, hc⟩ := List.mem_flatMap.mp hc
    have hm := (fullBases_perm hc).mem_iff.mp ha
    rcases List.mem_cons.mp hm with rfl | ha
    · exact ⟨by omega, by omega⟩
    · have ho := ih old hold a ha
      exact ⟨by omega, ho.2⟩

theorem circles_valid (baseCircles : List (List Nat))
    (hv : CircleFamilyValid 11 baseCircles) (hs : CircleSupport 0 baseCircles) (k : Nat) :
    CircleFamilyValid (k + 11) (circles baseCircles k) := by
  induction k with
  | zero => exact hv
  | succ k ih =>
    exact ih.extend (k + 14) (fun c hc ha => by
      have := (circles_support baseCircles hs k c hc (k + 14) ha).1
      omega)

theorem circles_length (baseCircles : List (List Nat))
    (hv : CircleFamilyValid 11 baseCircles) (hs : CircleSupport 0 baseCircles) (k : Nat) :
    (circles baseCircles k).length = circleCount baseCircles.length k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [circles, extendCircles_length (k + 11) _ _
      (fun c hc => (circles_valid baseCircles hv hs k c hc).1), ih]
    rfl

theorem circleCount_factorial (c0 k : Nat) :
    3628800 * circleCount c0 k = c0 * (k + 10).factorial := by
  induction k with
  | zero => simp [circleCount, Nat.factorial, Nat.mul_comm]
  | succ k ih =>
    change 3628800 * ((k + 11) * circleCount c0 k) = _
    rw [show (k + 1 + 10).factorial = (k + 11) * (k + 10).factorial from Nat.factorial_succ (k + 10)]
    calc
      3628800 * ((k + 11) * circleCount c0 k) = (k + 11) * (3628800 * circleCount c0 k) := by ring
      _ = (k + 11) * (c0 * (k + 10).factorial) := by rw [ih]
      _ = c0 * ((k + 11) * (k + 10).factorial) := by ring

theorem circles_length_factorial (baseCircles : List (List Nat))
    (hv : CircleFamilyValid 11 baseCircles) (hs : CircleSupport 0 baseCircles) (k : Nat) :
    3628800 * (circles baseCircles k).length = baseCircles.length * (k + 10).factorial := by
  rw [circles_length baseCircles hv hs k]
  exact circleCount_factorial baseCircles.length k

/-- The designated completed macro trails at a stage have the same occurrence
index type as the next transport family. -/
def completedFamily (baseFamily : I0 → List (Row Nat)) (k : Nat) : Index I0 (k + 1) → List (Row Nat) :=
  fun ip => completionWalk (family baseFamily k ip.1) 13 ip.2.val

/-- Completion preserves closure for each individual returning port walk. -/
theorem completionWalk_closed {rs : List (Row Nat)} (hc : ClosedTrail rs)
    (h : Nat) (hn : 3 ≤ h + 1)
    (hlen : ∀ r ∈ rs, r.base.length = h + 1)
    (hkind : ∀ r ∈ rs, r.visible = r.base.length ∨ r.visible = r.base.length - 2)
    (hw : (h : Int) ∣ signedExcess rs) (p : Nat) (hp : p < h) :
    ClosedTrail (completionWalk rs 13 p) := by
  have hne := completionWalk_nonempty rs 13 p hc.1
  have hchain : RowTrailCompatible (rs.head hc.1) rs.tail := by
    cases rs with
    | nil => exact False.elim (hc.1 rfl)
    | cons r rs => exact closedTrail_internal hc
  have hi := completionWalk_internal rs hc.1 13 (h + 1) p hn (by omega) hlen hkind hchain
  have hb : ((completionWalk rs 13 p).getLast hne).Compatible ((completionWalk rs 13 p).head hne) := by
    change _ = _
    rw [completionWalk_last_tail rs hc.1 13 (h + 1) p hn (by omega) hlen hkind,
      completionWalk_head rs hc.1 13 (h + 1) p hn (by omega) hlen hkind,
      completionExit_eq_self_of_winding rs h hn hlen hkind hw p hp,
      closedTrail_last_compatible_head hc]
  have hr := pathRunsTo_of_path_spec _ _ hne hi hb
  obtain ⟨a, as, he⟩ := List.exists_cons_of_ne_nil hne
  simp only [he, List.head_cons] at hr
  rw [he]
  exact closedTrail_of_pathRunsTo hr


end SuperpermutationUpperBound.Native14.Iteration
