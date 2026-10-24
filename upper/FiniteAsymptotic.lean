module

public import UpperBoundProof.Statement
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

/-!
The arithmetic end of the improved upper construction.
Adapted from Pantone's certified `GenericBounds` and `AsymptoticEpsilon`.
The finite-word premise remains explicit until the new base is certified.
-/
namespace SuperpermutationBounds.ImprovedUpper
set_option maxHeartbeats 2000000

def Fourth (K : Nat) : Nat := (K - 3).factorial

def bound (m a : Nat) : ℚ :=
  F3 (m + 2) + (926683 / 1814400 : ℚ) * ((m - 1).factorial : ℚ) +
    ((a - 2 : Nat) : ℚ) * (30571 / 1814400 : ℚ) * ((m - 1).factorial : ℚ) /
      ((m - 1 : Nat) : ℚ) +
    ((m - a : Nat) : ℚ) * min
      ((30571 / 1814400 : ℚ) * ((m - 1).factorial : ℚ) / ((m - 1 : Nat) : ℚ))
      (((m + 1).factorial : ℚ) / ((a + 1).factorial : ℚ))

def FiniteStatement : Prop :=
  ∀ m : Nat, 12 ≤ m → ∀ a : Nat, 2 ≤ a → a ≤ m →
    ∃ w : List (Fin (m + 2)), Covers w ∧ (w.length : ℚ) ≤ bound m a

def AsymptoticStatement : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : Nat, 14 ≤ N ∧
    ∀ K : Nat, N ≤ K → ∃ w : List (Fin K), Covers w ∧
      (w.length : ℚ) ≤ F3 K + ((926683 : ℚ) / 1814400 + ε) * (Fourth K : ℚ)

/-- Four late factorial factors suffice; no asymptotic factorial estimate is used. -/
theorem factorial_four_power_bound (a : Nat) (ha : 4 ≤ a) :
    (a : ℚ) ^ 4 ≤ 16 * (Nat.factorial (a + 1) : ℚ) := by
  have hf := Nat.factorial_mul_pow_le_factorial (m := a - 3) (n := 4)
  have he₁ : a - 3 + 1 = a - 2 := by omega
  have he₂ : a - 3 + 4 = a + 1 := by omega
  rw [he₁, he₂] at hf
  have hp : (a - 2) ^ 4 ≤ Nat.factorial (a + 1) :=
    (Nat.le_mul_of_pos_left _ (Nat.factorial_pos (a - 3))).trans hf
  have hpq : ((a - 2 : Nat) : ℚ) ^ 4 ≤ (Nat.factorial (a + 1) : ℚ) := by
    exact_mod_cast hp
  have hsmall : (a : ℚ) ≤ 2 * ((a - 2 : Nat) : ℚ) := by
    have he : ((a - 2 : Nat) : ℚ) = (a : ℚ) - 2 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [he]
    have haq : (4 : ℚ) ≤ a := by exact_mod_cast ha
    linarith
  calc
    (a : ℚ) ^ 4 ≤ (2 * ((a - 2 : Nat) : ℚ)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hsmall 4
    _ = 16 * ((a - 2 : Nat) : ℚ) ^ 4 := by ring
    _ ≤ 16 * (Nat.factorial (a + 1) : ℚ) := mul_le_mul_of_nonneg_left hpq (by norm_num)

/-- Natural division provides both the needed upper and lower estimates. -/
theorem floor_parameter_bounds (m r : Nat) (hr : 1 ≤ r) (hm : 8 * r ≤ m) :
    8 ≤ m / r ∧ m / r ≤ m ∧ (m / r) * r ≤ m ∧ m ≤ 2 * r * (m / r) := by
  have ha : 8 ≤ m / r := (Nat.le_div_iff_mul_le (by omega)).mpr hm
  have hupper := Nat.div_mul_le_self m r
  have hlower := Nat.lt_div_mul_add (a := m) (b := r) (by omega)
  refine ⟨ha, Nat.div_le_self _ _, hupper, ?_⟩
  nlinarith

/-- Coarse normalized error from the factorial option in the minimum. -/
theorem factorial_error_le (m a r : Nat) (hm : 1 ≤ m) (ha : 4 ≤ a)
    (hma : m ≤ 2 * r * a) :
    (m : ℚ) * m * (m + 1) / (Nat.factorial (a + 1) : ℚ) ≤
      512 * (r : ℚ) ^ 4 / m := by
  have hmq : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hmaQ : (m : ℚ) ≤ 2 * r * a := by exact_mod_cast hma
  have hf : (0 : ℚ) < Nat.factorial (a + 1) := by exact_mod_cast Nat.factorial_pos (a + 1)
  have hfour : (m : ℚ) ^ 4 ≤ 256 * (r : ℚ) ^ 4 * (Nat.factorial (a + 1) : ℚ) := by
    calc
      (m : ℚ) ^ 4 ≤ (2 * (r : ℚ) * a) ^ 4 := pow_le_pow_left₀ (by positivity) hmaQ 4
      _ = 16 * (r : ℚ) ^ 4 * (a : ℚ) ^ 4 := by ring
      _ ≤ 16 * (r : ℚ) ^ 4 * (16 * (Nat.factorial (a + 1) : ℚ)) :=
        mul_le_mul_of_nonneg_left (factorial_four_power_bound a ha) (by positivity)
      _ = _ := by ring
  apply (div_le_div_iff₀ hf (by linarith : (0 : ℚ) < m)).mpr
  calc
    (m : ℚ) * m * (m + 1) * m ≤ (m : ℚ) * m * (2 * m) * m := by
      gcongr
      linarith
    _ = 2 * (m : ℚ) ^ 4 := by ring
    _ ≤ 512 * (r : ℚ) ^ 4 * (Nat.factorial (a + 1) : ℚ) := by linarith

/-- The linear-overlap error is at most 2/r, using gamma <= 1. -/
theorem linear_error_le (m a r : Nat) (hm : 2 ≤ m) (hr : 1 ≤ r)
    (har : a * r ≤ m) :
    ((a - 2 : Nat) : ℚ) * ((30571 : ℚ) / 1814400) / ((m - 1 : Nat) : ℚ) ≤
      2 / (r : ℚ) := by
  have hmQ : (2 : ℚ) ≤ m := by exact_mod_cast hm
  have hrQ : (0 : ℚ) < r := by exact_mod_cast (show 0 < r by omega)
  have harQ : (a : ℚ) * r ≤ m := by exact_mod_cast har
  have hd : ((m - 1 : Nat) : ℚ) = (m : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hn : ((a - 2 : Nat) : ℚ) * ((30571 : ℚ) / 1814400) ≤ a := by
    have hsub : ((a - 2 : Nat) : ℚ) ≤ a := by exact_mod_cast Nat.sub_le a 2
    have hmul := mul_le_mul_of_nonneg_left
      (by norm_num : (30571 : ℚ) / 1814400 ≤ 1) (show (0 : ℚ) ≤ ((a - 2 : Nat) : ℚ) by positivity)
    have hm' : ((a - 2 : Nat) : ℚ) * ((30571 : ℚ) / 1814400) ≤ ((a - 2 : Nat) : ℚ) := by
      simpa only [mul_one] using hmul
    exact hm'.trans hsub
  rw [hd]
  apply (div_le_div_iff₀ (by linarith : (0 : ℚ) < (m : ℚ) - 1) hrQ).mpr
  have hnR := mul_le_mul_of_nonneg_right hn (le_of_lt hrQ)
  linarith

/-- With a=floor(m/r), both errors have an explicit elementary majorant. -/
theorem bound_floor_majorant (m r : Nat) (hr : 1 ≤ r) (hm : 8 * r ≤ m) :
    bound m (m / r) ≤
      (F3 (m + 2) : ℚ) +
        ((926683 : ℚ) / 1814400 + 2 / (r : ℚ) + 512 * (r : ℚ) ^ 4 / m) *
          (Fourth (m + 2) : ℚ) := by
  have hb := floor_parameter_bounds m r hr hm
  have hm2 : 2 ≤ m := by omega
  have hlinear := linear_error_le m (m / r) r hm2 hr hb.2.2.1
  have hfactorial := factorial_error_le m (m / r) r (by omega) (by omega) hb.2.2.2
  have hfac : (Nat.factorial (m + 1) : ℚ) =
      ((m : ℚ) + 1) * m * (Nat.factorial (m - 1) : ℚ) := by
    rw [Nat.factorial_succ, ← Nat.mul_factorial_pred (n := m) (by omega)]
    push_cast
    ring
  have htail :
      ((m - m / r : Nat) : ℚ) *
          min (((30571 : ℚ) / 1814400) * (Nat.factorial (m - 1) : ℚ) / ((m - 1 : Nat) : ℚ))
            ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / r + 1) : ℚ)) ≤
        (m : ℚ) * ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / r + 1) : ℚ)) := by
    apply (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.sub_le m (m / r)
  have hFourth : (m + 2) - 3 = m - 1 := by omega
  unfold bound
  rw [Fourth, hFourth]
  calc
    _ ≤ (F3 (m + 2) : ℚ) + ((926683 : ℚ) / 1814400) * (Nat.factorial (m - 1) : ℚ) +
          ((m / r - 2 : Nat) : ℚ) * ((30571 : ℚ) / 1814400) * (Nat.factorial (m - 1) : ℚ)
            / ((m - 1 : Nat) : ℚ) +
          (m : ℚ) * ((Nat.factorial (m + 1) : ℚ) / (Nat.factorial (m / r + 1) : ℚ)) :=
      add_le_add (le_refl _) htail
    _ = (F3 (m + 2) : ℚ) +
          ((926683 : ℚ) / 1814400 +
            ((m / r - 2 : Nat) : ℚ) * ((30571 : ℚ) / 1814400) / ((m - 1 : Nat) : ℚ) +
            (m : ℚ) * m * (m + 1) / (Nat.factorial (m / r + 1) : ℚ)) *
          (Nat.factorial (m - 1) : ℚ) := by
      rw [hfac]
      ring
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact add_le_add (add_le_add (le_refl _) hlinear) hfactorial

/-- The finite circle construction implies the exact rational-epsilon target.
This theorem is conditional on actual finite-parameter word existence. -/
theorem asymptotic_of_finite (hcircle : FiniteStatement) :
    AsymptoticStatement := by
  intro ε hε
  obtain ⟨r, hr⟩ := exists_nat_gt ((4 : ℚ) / ε)
  have hrpos : (0 : ℚ) < r := lt_trans (by positivity) hr
  have hrNat : 1 ≤ r := by exact_mod_cast hrpos
  have hsmall : (2 : ℚ) / r ≤ ε / 2 := by
    apply (div_le_iff₀ hrpos).mpr
    have hh := (div_lt_iff₀ hε).mp hr
    nlinarith
  obtain ⟨M, hM⟩ := exists_nat_gt ((1024 : ℚ) * (r : ℚ) ^ 4 / ε)
  refine ⟨14 + 8 * r + M, by omega, ?_⟩
  intro K hK
  have hm9 : 12 ≤ K - 2 := by omega
  have hmr : 8 * r ≤ K - 2 := by omega
  have hmM : M ≤ K - 2 := by omega
  have hmpos : (0 : ℚ) < ((K - 2 : Nat) : ℚ) := by exact_mod_cast (show 0 < K - 2 by omega)
  have hlarge : 512 * (r : ℚ) ^ 4 / ((K - 2 : Nat) : ℚ) ≤ ε / 2 := by
    apply (div_le_iff₀ hmpos).mpr
    have hbound : (1024 : ℚ) * (r : ℚ) ^ 4 / ε < ((K - 2 : Nat) : ℚ) :=
      hM.trans_le (by exact_mod_cast hmM)
    have hh := (div_lt_iff₀ hε).mp hbound
    nlinarith
  have hb := floor_parameter_bounds (K - 2) r hrNat hmr
  obtain ⟨w, hw, hlen⟩ := hcircle (K - 2) hm9 ((K - 2) / r) (by omega) hb.2.1
  have hlength : (w.length : ℚ) ≤
      (F3 ((K - 2) + 2) : ℚ) +
        ((926683 : ℚ) / 1814400 + ε) * (Fourth ((K - 2) + 2) : ℚ) := by
    apply hlen.trans
    apply (bound_floor_majorant (K - 2) r hrNat hmr).trans
    apply add_le_add (le_refl _)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  have hKeq : K - 2 + 2 = K := by omega
  have hout : ∃ w : List (Fin (K - 2 + 2)), Covers w ∧
      (w.length : ℚ) ≤ (F3 (K - 2 + 2) : ℚ) +
        ((926683 : ℚ) / 1814400 + ε) * (Fourth (K - 2 + 2) : ℚ) := ⟨w, hw, hlength⟩
  exact Eq.mp (congrArg (fun n => ∃ w : List (Fin n), Covers w ∧
      (w.length : ℚ) ≤ (F3 n : ℚ) +
        ((926683 : ℚ) / 1814400 + ε) * (Fourth n : ℚ)) hKeq) hout


end SuperpermutationBounds.ImprovedUpper
