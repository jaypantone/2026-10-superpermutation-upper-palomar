module

public import upper.certificate.NativeCircles00
public import upper.certificate.NativeCircles01
public import upper.certificate.NativeCircles02
public import upper.certificate.NativeCircles03
public import upper.certificate.NativeCircles04
public import upper.certificate.NativeCircles05
public import upper.certificate.NativeCircles06
public import upper.certificate.NativeCircles07
public import upper.certificate.NativeCircles08
public import upper.certificate.NativeCircles09
public import upper.certificate.NativeCircles10
public import upper.certificate.NativeCircles11
public import upper.certificate.NativeCircles12
public import upper.certificate.NativeCircles13
public import upper.certificate.NativeCircles14
public import upper.certificate.NativeCircles15
public import upper.certificate.NativeCircles16
public import upper.certificate.NativeCircles17
public import upper.certificate.NativeCircles18
public import upper.certificate.NativeCircles19
public import upper.certificate.NativeCircles20
public import upper.certificate.NativeCircles21
public import upper.certificate.NativeCircles22
public import upper.certificate.NativeCircles23
public import upper.certificate.NativeCircles24
public import upper.certificate.NativeCircles25
public import upper.certificate.NativeCircles26
public import upper.certificate.NativeCircles27
public import upper.certificate.NativeCircles28

@[expose] public section

/-! All 14774 native final-letter connector occurrences, in source order. -/
namespace SuperpermutationUpperBound.Native14.Certificate.NativeCircleData
open CircleTransport

noncomputable def chunks : List (List (List Nat)) := [NativeCircles00.circles, NativeCircles01.circles, NativeCircles02.circles, NativeCircles03.circles, NativeCircles04.circles, NativeCircles05.circles, NativeCircles06.circles, NativeCircles07.circles, NativeCircles08.circles, NativeCircles09.circles, NativeCircles10.circles, NativeCircles11.circles, NativeCircles12.circles, NativeCircles13.circles, NativeCircles14.circles, NativeCircles15.circles, NativeCircles16.circles, NativeCircles17.circles, NativeCircles18.circles, NativeCircles19.circles, NativeCircles20.circles, NativeCircles21.circles, NativeCircles22.circles, NativeCircles23.circles, NativeCircles24.circles, NativeCircles25.circles, NativeCircles26.circles, NativeCircles27.circles, NativeCircles28.circles]
noncomputable def circles : List (List Nat) := chunks.flatten

theorem circles_length : circles.length = 14774 := by
  simp only [circles, chunks, List.flatten_cons, List.flatten_nil, List.length_append,
    List.length_nil, NativeCircles00.circles_length, NativeCircles01.circles_length, NativeCircles02.circles_length, NativeCircles03.circles_length, NativeCircles04.circles_length, NativeCircles05.circles_length, NativeCircles06.circles_length, NativeCircles07.circles_length, NativeCircles08.circles_length, NativeCircles09.circles_length, NativeCircles10.circles_length, NativeCircles11.circles_length, NativeCircles12.circles_length, NativeCircles13.circles_length, NativeCircles14.circles_length, NativeCircles15.circles_length, NativeCircles16.circles_length, NativeCircles17.circles_length, NativeCircles18.circles_length, NativeCircles19.circles_length, NativeCircles20.circles_length, NativeCircles21.circles_length, NativeCircles22.circles_length, NativeCircles23.circles_length, NativeCircles24.circles_length, NativeCircles25.circles_length, NativeCircles26.circles_length, NativeCircles27.circles_length, NativeCircles28.circles_length]

theorem circles_check : nativeCircleCheck circles = true := by
  simp only [circles, chunks, nativeCircleCheck, List.flatten_cons, List.flatten_nil,
    List.all_append, List.all_nil, Bool.and_true, Bool.and_eq_true]
  repeat' apply And.intro
  · exact NativeCircles00.circles_check
  · exact NativeCircles01.circles_check
  · exact NativeCircles02.circles_check
  · exact NativeCircles03.circles_check
  · exact NativeCircles04.circles_check
  · exact NativeCircles05.circles_check
  · exact NativeCircles06.circles_check
  · exact NativeCircles07.circles_check
  · exact NativeCircles08.circles_check
  · exact NativeCircles09.circles_check
  · exact NativeCircles10.circles_check
  · exact NativeCircles11.circles_check
  · exact NativeCircles12.circles_check
  · exact NativeCircles13.circles_check
  · exact NativeCircles14.circles_check
  · exact NativeCircles15.circles_check
  · exact NativeCircles16.circles_check
  · exact NativeCircles17.circles_check
  · exact NativeCircles18.circles_check
  · exact NativeCircles19.circles_check
  · exact NativeCircles20.circles_check
  · exact NativeCircles21.circles_check
  · exact NativeCircles22.circles_check
  · exact NativeCircles23.circles_check
  · exact NativeCircles24.circles_check
  · exact NativeCircles25.circles_check
  · exact NativeCircles26.circles_check
  · exact NativeCircles27.circles_check
  · exact NativeCircles28.circles_check

theorem circles_valid : CircleFamilyValid 11 circles :=
  nativeCircles_valid_of_check circles_check

theorem circles_final : ∀ c ∈ circles, 13 ∈ c :=
  nativeCircles_final_of_check circles_check

theorem circles_support : Iteration.CircleSupport 0 circles :=
  nativeCircles_support_of_check circles_check


/-- Bounded lookup: at most 29 chunk cells and 512 circle cells are traversed. -/
noncomputable def circleAt (i : Nat) : List Nat :=
  (chunks.getD (i / 512) []).getD (i % 512) []

theorem chunks_length : chunks.length = 29 := by rfl

theorem chunk_lengths : chunks.map List.length = List.replicate 28 512 ++ [438] := by
  simp only [chunks, List.map_cons, List.map_nil,
    NativeCircles00.circles_length, NativeCircles01.circles_length,
    NativeCircles02.circles_length, NativeCircles03.circles_length,
    NativeCircles04.circles_length, NativeCircles05.circles_length,
    NativeCircles06.circles_length, NativeCircles07.circles_length,
    NativeCircles08.circles_length, NativeCircles09.circles_length,
    NativeCircles10.circles_length, NativeCircles11.circles_length,
    NativeCircles12.circles_length, NativeCircles13.circles_length,
    NativeCircles14.circles_length, NativeCircles15.circles_length,
    NativeCircles16.circles_length, NativeCircles17.circles_length,
    NativeCircles18.circles_length, NativeCircles19.circles_length,
    NativeCircles20.circles_length, NativeCircles21.circles_length,
    NativeCircles22.circles_length, NativeCircles23.circles_length,
    NativeCircles24.circles_length, NativeCircles25.circles_length,
    NativeCircles26.circles_length, NativeCircles27.circles_length,
    NativeCircles28.circles_length]
  rfl

theorem circleAt_mem (i : Nat) (hi : i < 14774) : circleAt i ∈ circles := by
  have hq : i / 512 < chunks.length := by rw [chunks_length]; omega
  have hchunk : chunks.getD (i / 512) [] ∈ chunks := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq,
      Option.getD_some] using (List.getElem_mem hq)
  have hlen : (chunks.getD (i / 512) []).length =
      (List.replicate 28 512 ++ [438]).getD (i / 512) 0 := by
    rw [← chunk_lengths]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases chunks[i / 512]? <;> rfl
  have hr : i % 512 < (chunks.getD (i / 512) []).length := by
    rw [hlen]
    by_cases hsmall : i / 512 < 28
    · have hrep : i / 512 < (List.replicate 28 512).length := by simpa using hsmall
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hrep,
        List.getElem?_eq_getElem hrep, List.getElem_replicate, Option.getD_some]
      exact Nat.mod_lt _ (by decide)
    · have he : i / 512 = 28 := by rw [chunks_length] at hq; omega
      rw [he]
      change i % 512 < 438
      have hd := Nat.mod_add_div i 512
      omega
  apply List.mem_flatten.mpr
  refine ⟨chunks.getD (i / 512) [], hchunk, ?_⟩
  change ((chunks.getD (i / 512) [])[i % 512]?).getD [] ∈ chunks.getD (i / 512) []
  rw [List.getElem?_eq_getElem hr]
  exact List.getElem_mem hr

theorem circleAt_length (i : Nat) (hi : i < 14774) : (circleAt i).length = 11 :=
  (circles_valid _ (circleAt_mem i hi)).1

theorem circleAt_final (i : Nat) (hi : i < 14774) : 13 ∈ circleAt i :=
  circles_final _ (circleAt_mem i hi)

end SuperpermutationUpperBound.Native14.Certificate.NativeCircleData
