module

public import upper.FiniteAsymptotic

@[expose] public section

/-! Numerical and coefficient consequences. Finite word existence remains
an explicit premise until the native base is fully certified. -/
namespace SuperpermutationBounds.ImprovedUpper

theorem coefficient_decomposition :
    (889 / 1800 : ℚ) + 30571 / 1814400 = 926683 / 1814400 := by norm_num

theorem improvement_on_43_80 :
    (43 / 80 : ℚ) - 926683 / 1814400 = 48557 / 1814400 := by norm_num

theorem coefficient_below_43_80 :
    (926683 / 1814400 : ℚ) < 43 / 80 := by norm_num

theorem coefficient_above_half :
    (1 / 2 : ℚ) < 926683 / 1814400 := by norm_num

theorem word_14_of_finite (h : FiniteStatement) : HasWord 14 93905133768 := by
  obtain ⟨w, hw, hl⟩ := h 12 (by decide) 9 (by decide) (by decide)
  have hb : bound 12 9 = (93905133768 : ℚ) := by
    norm_num [bound, F3, Nat.factorial]
  rw [hb] at hl
  exact ⟨w, hw, by exact_mod_cast hl⟩

theorem word_15_of_finite (h : FiniteStatement) : HasWord 15 1401329128342 := by
  obtain ⟨w, hw, hl⟩ := h 13 (by decide) 9 (by decide) (by decide)
  have hb : bound 13 9 = (1401329128342 : ℚ) := by
    norm_num [bound, F3, Nat.factorial]
  rw [hb] at hl
  exact ⟨w, hw, by exact_mod_cast hl⟩

theorem word_16_of_finite (h : FiniteStatement) : HasWord 16 22320881220264 := by
  obtain ⟨w, hw, hl⟩ := h 14 (by decide) 9 (by decide) (by decide)
  have hb : bound 14 9 = (22320881220264 : ℚ) := by
    norm_num [bound, F3, Nat.factorial]
  rw [hb] at hl
  exact ⟨w, hw, by exact_mod_cast hl⟩

theorem word_17_of_finite (h : FiniteStatement) : HasWord 17 377963186649048 := by
  obtain ⟨w, hw, hl⟩ := h 15 (by decide) 9 (by decide) (by decide)
  have hb : bound 15 9 = (377963186649048 : ℚ) := by
    norm_num [bound, F3, Nat.factorial]
  rw [hb] at hl
  exact ⟨w, hw, by exact_mod_cast hl⟩

theorem word_18_of_finite (h : FiniteStatement) : HasWord 18 6779662770937056 := by
  obtain ⟨w, hw, hl⟩ := h 16 (by decide) 9 (by decide) (by decide)
  have hb : bound 16 9 = (6779662770937056 : ℚ) := by
    norm_num [bound, F3, Nat.factorial]
  rw [hb] at hl
  exact ⟨w, hw, by exact_mod_cast hl⟩

theorem word_19_of_finite (h : FiniteStatement) : HasWord 19 128414015952702480 := by
  obtain ⟨w, hw, hl⟩ := h 17 (by decide) 9 (by decide) (by decide)
  have hb : bound 17 9 = (128414015952702480 : ℚ) := by
    norm_num [bound, F3, Nat.factorial]
  rw [hb] at hl
  exact ⟨w, hw, by exact_mod_cast hl⟩

theorem word_20_of_finite (h : FiniteStatement) : HasWord 20 2561133914781361920 := by
  obtain ⟨w, hw, hl⟩ := h 18 (by decide) 9 (by decide) (by decide)
  have hb : bound 18 9 = (2561133914781361920 : ℚ) := by
    norm_num [bound, F3, Nat.factorial]
  rw [hb] at hl
  exact ⟨w, hw, by exact_mod_cast hl⟩

end SuperpermutationBounds.ImprovedUpper
