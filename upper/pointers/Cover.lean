module

public import upper.pointers.Table
public import upper.connectors.Ordinary

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Pointers
open CircleTransport Transport SeedFamily Certificate

noncomputable def circles : List (List Nat) :=
  Connectors.Ordinary.circles ++ NativeCircleData.circles

theorem circles_length : circles.length = 61142 := by
  simp only [circles,List.length_append,Connectors.Ordinary.circles_length,
    NativeCircleData.circles_length]

theorem circles_valid : CircleFamilyValid 11 circles := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact Connectors.Ordinary.circles_valid c hc
  · exact NativeCircleData.circles_valid c hc

theorem circles_support : Iteration.CircleSupport 0 circles := by
  intro c hc a ha
  rcases List.mem_append.mp hc with hc | hc
  · exact Connectors.Ordinary.circles_support c hc a ha
  · exact NativeCircleData.circles_support c hc a ha

theorem mixed_cover (i : Nat) (hi : i<11136) (j : Fin 11) :
    ∃c∈NativeCircleData.circles,SafeIncidence (parentAt i) 13 j c := by
  obtain ⟨w,hw⟩ := Table.all_checked (11*i+j.val) (by omega)
  have hc := checkEntry_sound FastCircles.circleAt NativeCircleData.circles
    FastCircles.circleAt_mem (11*i+j.val) w hw
  have hi' : (11*i+j.val)/11=i := by omega
  have hj : completionPort (11*i+j.val)=j := by
    apply Fin.ext
    simp only [completionPort]
    omega
  simpa only [hi',hj] using hc

theorem safe_cover : SafeCircleCover SeedFamily.family 13 11 circles := by
  intro i j
  rcases family_cases_index i with ⟨k,hk,he⟩ | ⟨x,hx,y,hy,he⟩
  · obtain ⟨c,hc,hs⟩ := mixed_cover k hk j
    exact ⟨c,List.mem_append_right _ hc,he.symm ▸ hs⟩
  · obtain ⟨c,hc,hs⟩ := Connectors.Ordinary.cover hx hy j
    exact ⟨c,List.mem_append_left _ hc,he.symm ▸ hs⟩

end SuperpermutationUpperBound.Native14.Pointers
