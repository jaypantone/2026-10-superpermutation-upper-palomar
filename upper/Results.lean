module

public import upper.Base
public import upper.Construction
public import upper.Consequences

@[expose] public section

/-! Unconditional word-existence consequences of the kernel-checked finite certificate. -/
namespace SuperpermutationBounds.ImprovedUpper
open SuperpermutationUpperBound.Native14

theorem finite_bound : FiniteStatement := Bounds.finite_of_base nativeBase

theorem asymptotic_bound : AsymptoticStatement := asymptotic_of_finite finite_bound

theorem word_14 : HasWord 14 93905133768 := word_14_of_finite finite_bound
theorem word_15 : HasWord 15 1401329128342 := word_15_of_finite finite_bound
theorem word_16 : HasWord 16 22320881220264 := word_16_of_finite finite_bound
theorem word_17 : HasWord 17 377963186649048 := word_17_of_finite finite_bound
theorem word_18 : HasWord 18 6779662770937056 := word_18_of_finite finite_bound
theorem word_19 : HasWord 19 128414015952702480 := word_19_of_finite finite_bound
theorem word_20 : HasWord 20 2561133914781361920 := word_20_of_finite finite_bound

end SuperpermutationBounds.ImprovedUpper
