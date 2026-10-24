module

public import upper.Family
public import upper.FiniteAsymptotic
public import SuperpermutationUpperBound.Assembly.CircleRows

@[expose] public section

/-! Native n14 finite and eventual construction from a semantic certificate.
The finite Base argument is explicit; this file does not fabricate it.
Adapted from Pantone's GenericBounds/CircleCounts/CircleRational. -/
namespace SuperpermutationUpperBound.Native14.Bounds
open SuperpermutationBounds.ImprovedUpper
set_option maxHeartbeats 2000000

def f3Nat (K : Nat) : Nat := K.factorial + (K - 1).factorial + (K - 2).factorial

@[simp] theorem f3_cast (K : Nat) : (f3Nat K : ℚ) = SuperpermutationBounds.F3 K := by
  simp [f3Nat, SuperpermutationBounds.F3]

theorem overlap_state_count_rat (k a : Nat) (ha : a ≤ k + 12) :
    ((k + 13).descFactorial (k + 12 - a) : ℚ) =
      ((k + 13).factorial : ℚ) / ((a + 1).factorial : ℚ) := by
  have hfact : ((a + 1).factorial : ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hfact).mpr
  have he := Nat.factorial_mul_descFactorial (show k + 12 - a ≤ k + 13 by omega)
  rw [show k + 13 - (k + 12 - a) = a + 1 by omega] at he
  exact_mod_cast (Nat.mul_comm _ _).trans he

/-- The final overlap charge decreases with every available join. -/
theorem circle_overlap_length_bound {base m a t J c V len : Nat}
    (ha : 2 ≤ a) (ham : a ≤ m) (ht : t ≤ c) (hj : J ≤ min t V)
    (hlen : len = base + (m - 2) * t - (m - a) * (t - J)) :
    len ≤ base + (a - 2) * c + (m - a) * min c V := by
  have hJt := (Nat.le_min.mp hj).1
  have hJV := (Nat.le_min.mp hj).2
  have hJc : J ≤ c := hJt.trans ht
  have hmin : J ≤ min c V := Nat.le_min.mpr ⟨hJc, hJV⟩
  have h1 := Nat.mul_le_mul_left (a - 2) ht
  have h2 := Nat.mul_le_mul_left (m - a) hmin
  have hsplit : m - 2 = (a - 2) + (m - a) := by omega
  have he : base + (m - 2) * t =
      base + (a - 2) * t + (m - a) * J + (m - a) * (t - J) := by
    rw [hsplit]
    have hsub : t = J + (t - J) := by omega
    nlinarith
  rw [he, Nat.add_sub_cancel] at hlen
  omega

/-- The integer ledger produced by closed row assembly and overlap joins. -/
def ledger (k a q c : Nat) : Nat :=
  f3Nat (k + 14) + q + (k + 11) * c + (a - 2) * c +
    (k + 12 - a) * min c ((k + 13).descFactorial (k + 12 - a))

theorem circle_count_scaled (k c : Nat)
    (hc : 3628800 * c = 61142 * (k + 10).factorial) :
    3628800 * ((k + 11) * c) = 61142 * (k + 11).factorial := by
  rw [show (k + 11).factorial = (k + 11) * (k + 10).factorial from
    Nat.factorial_succ (k + 10)]
  nlinarith

theorem circle_count_rat (k c : Nat)
    (hc : 3628800 * c = 61142 * (k + 10).factorial) :
    (c : ℚ) = (30571 / 1814400 : ℚ) * ((k + 11).factorial : ℚ) / (k + 11 : Nat) := by
  have hk : ((k + 11 : Nat) : ℚ) ≠ 0 := by positivity
  apply (eq_div_iff hk).mpr
  have he : (3628800 : ℚ) * (((k + 11 : Nat) : ℚ) * (c : ℚ)) =
      61142 * ((k + 11).factorial : ℚ) := by
    exact_mod_cast circle_count_scaled k c hc
  linarith

theorem principal_numerator (k q c : Nat)
    (hq : 1800 * q = 889 * (k + 11).factorial)
    (hc : 3628800 * c = 61142 * (k + 10).factorial) :
    1814400 * (q + (k + 11) * c) = 926683 * (k + 11).factorial := by
  have he := circle_count_scaled k c hc
  omega

theorem principal_rat (k q c : Nat)
    (hq : 1800 * q = 889 * (k + 11).factorial)
    (hc : 3628800 * c = 61142 * (k + 10).factorial) :
    ((q + (k + 11) * c : Nat) : ℚ) = (926683 / 1814400 : ℚ) * ((k + 11).factorial : ℚ) := by
  have he : (1814400 : ℚ) * ((q + (k + 11) * c : Nat) : ℚ) =
      926683 * ((k + 11).factorial : ℚ) := by
    exact_mod_cast principal_numerator k q c hq hc
  linarith

theorem ledger_eq_bound (k a q c : Nat) (ha : a ≤ k + 12)
    (hq : 1800 * q = 889 * (k + 11).factorial)
    (hc : 3628800 * c = 61142 * (k + 10).factorial) :
    (ledger k a q c : ℚ) = bound (k + 12) a := by
  have hp := principal_rat k q c hq hc
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hp
  unfold ledger bound
  rw [← f3_cast]
  rw [show k + 12 + 2 = k + 14 by omega, show k + 12 - 1 = k + 11 by omega,
    show k + 12 + 1 = k + 13 by omega]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_min, Nat.cast_ofNat]
  rw [show (f3Nat (k + 14) : ℚ) + (q : ℚ) + ((k : ℚ) + 11) * (c : ℚ) =
      (f3Nat (k + 14) : ℚ) + (926683 / 1814400 : ℚ) * ((k + 11).factorial : ℚ) by linarith]
  rw [circle_count_rat k c hc,
    overlap_state_count_rat k a ha]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  ring

theorem bound_of_nat_ledger (k a q c len : Nat) (ha : a ≤ k + 12)
    (hq : 1800 * q = 889 * (k + 11).factorial)
    (hc : 3628800 * c = 61142 * (k + 10).factorial)
    (hl : len ≤ ledger k a q c) : (len : ℚ) ≤ bound (k + 12) a := by
  rw [← ledger_eq_bound k a q c ha hq hc]
  exact_mod_cast hl

/-- A certified circle-covered family supplies one actual word and the full
natural connector/cut ledger before optimizing its component count. -/
theorem family_word_ledger {I0 : Type} [Fintype I0] (B : Family.Base I0)
    (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 12) :
    ∃ t J : Nat, ∃ w : Word (k + 14), IsSuperpermutation w ∧
      t ≤ Family.selectedCircleCount k ∧
      J ≤ min t ((k + 13).descFactorial (k + 12 - a)) ∧
      w.length = f3Nat (k + 14) + ((Family.rows B k).map Row.charge).sum +
        (k + 11) * Family.selectedCircleCount k + (k + 10) * t - (k + 12 - a) * (t - J) := by
  let rows := Family.completedFamily B k
  let circles := Family.circles B k
  have hlen : ∀ i r, r ∈ rows i → r.base.length + 1 = k + 14 := by
    intro i r hr
    have h := (Family.completed_family_valid B k i hr).2
    omega
  have hv : ∀ i r, r ∈ rows i → 1 ≤ r.visible :=
    fun i r hr => (Family.completed_family_valid B k i hr).1.2.2.1
  have hc : CircleTransport.CircleFamilyValid (k + 14 - 3) circles := by
    simpa only [show k + 14 - 3 = k + 11 by omega] using Family.circles_valid B k
  obtain ⟨t, J, w, hw, ht, hJ, hl⟩ := exists_word_of_circle_rows rows circles
    (by omega : 4 ≤ k + 14) (by omega : k + 12 - a ≤ k + 14 - 3)
    hlen hv (Family.completed_family_closed B k) hc
    (Family.completed_family_circle_cover B k) (Alphabet.stateAlphabet k)
    (fun c hcc b hb => (Alphabet.stateAlphabet_mem k b).mpr
      (Family.circles_support B k c hcc b hb))
    (fun c hcc b hb => (Family.circles_support B k c hcc b hb).1)
    (fun i r hr => Family.completed_family_word_support B k i hr)
    (fun _ hp => Family.completed_family_cover_range B k hp)
  have hi := Family.completed_family_univ_inventory B k
  have hvisible := (hi.map Row.visible).sum_eq
  have hcount := hi.length_eq
  change (((Finset.univ.toList).flatMap rows).map Row.visible).sum = _ at hvisible
  change ((Finset.univ.toList).flatMap rows).length = _ at hcount
  rw [(Family.completedRows_counts B k).2.1] at hvisible
  rw [(Family.completedRows_counts B k).1] at hcount
  have hcnum : circles.length = Family.selectedCircleCount k := Family.circles_count B k
  rw [hvisible, hcount, hcnum] at hl
  refine ⟨t, J, w, hw, by rwa [hcnum] at ht,
    by simpa only [Alphabet.stateAlphabet_card] using hJ, ?_⟩
  rw [hl]
  simp only [f3Nat, show k + 14 - 1 = k + 13 by omega,
    show k + 14 - 2 = k + 12 by omega, show k + 14 - 3 = k + 11 by omega,
    show k + 14 - 4 = k + 10 by omega]
  rw [show (k + 14).factorial = (k + 14) * (k + 13).factorial from Nat.factorial_succ (k + 13)]
  congr 1
  ring

/-- Optimize the module and final trail counts in the actual word ledger. -/
theorem family_word_bound {I0 : Type} [Fintype I0] (B : Family.Base I0)
    (k a : Nat) (ha : 2 ≤ a) (ham : a ≤ k + 12) :
    ∃ w : Word (k + 14), IsSuperpermutation w ∧
      w.length ≤ f3Nat (k + 14) + ((Family.rows B k).map Row.charge).sum +
        (k + 11) * Family.selectedCircleCount k + (a - 2) * Family.selectedCircleCount k +
        (k + 12 - a) * min (Family.selectedCircleCount k)
          ((k + 13).descFactorial (k + 12 - a)) := by
  obtain ⟨t, J, w, hw, ht, hJ, hl⟩ := family_word_ledger B k a ha ham
  refine ⟨w, hw, circle_overlap_length_bound (m := k + 12) ha ham ht hJ ?_⟩
  simpa only [show k + 12 - 2 = k + 10 by omega] using hl


private theorem covers_of_construction {K : ℕ} {w : List (Fin K)}
    (h : IsSuperpermutation w) : SuperpermutationBounds.Covers w := by
  intro p hlength hnodup
  obtain ⟨u, v, heq⟩ := h p ⟨hlength, hnodup⟩
  exact ⟨u, v, heq.symm⟩

/-- A native14 semantic base supplies the improved all-size finite formula. -/
theorem finite_of_base {I0 : Type} [Fintype I0] (B : Family.Base I0) : FiniteStatement := by
  intro m hm a ha ham
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hak : a ≤ k + 12 := by omega
  obtain ⟨w, hw, hl⟩ := family_word_bound B k a ha hak
  have he : ∃ w : Word (k + 14), SuperpermutationBounds.Covers w ∧
      (w.length : ℚ) ≤ bound (k + 12) a :=
    ⟨w, covers_of_construction hw,
      bound_of_nat_ledger k a _ _ w.length hak (Family.rows_charge B k)
        (Family.selectedCircleCount_factorial k) hl⟩
  rw [Nat.add_comm 12 k]
  exact he

/-- The construction consequence still has a finite semantic Base premise. -/
theorem asymptotic_of_base {I0 : Type} [Fintype I0] (B : Family.Base I0) : AsymptoticStatement :=
  asymptotic_of_finite (finite_of_base B)

end SuperpermutationUpperBound.Native14.Bounds
