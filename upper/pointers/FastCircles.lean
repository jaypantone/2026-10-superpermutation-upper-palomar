module

public import upper.pointers.circle_chunks.C00
public import upper.pointers.circle_chunks.C01
public import upper.pointers.circle_chunks.C02
public import upper.pointers.circle_chunks.C03
public import upper.pointers.circle_chunks.C04
public import upper.pointers.circle_chunks.C05
public import upper.pointers.circle_chunks.C06
public import upper.pointers.circle_chunks.C07
public import upper.pointers.circle_chunks.C08
public import upper.pointers.circle_chunks.C09
public import upper.pointers.circle_chunks.C10
public import upper.pointers.circle_chunks.C11
public import upper.pointers.circle_chunks.C12
public import upper.pointers.circle_chunks.C13
public import upper.pointers.circle_chunks.C14
public import upper.pointers.circle_chunks.C15
public import upper.pointers.circle_chunks.C16
public import upper.pointers.circle_chunks.C17
public import upper.pointers.circle_chunks.C18
public import upper.pointers.circle_chunks.C19
public import upper.pointers.circle_chunks.C20
public import upper.pointers.circle_chunks.C21
public import upper.pointers.circle_chunks.C22
public import upper.pointers.circle_chunks.C23
public import upper.pointers.circle_chunks.C24
public import upper.pointers.circle_chunks.C25
public import upper.pointers.circle_chunks.C26
public import upper.pointers.circle_chunks.C27
public import upper.pointers.circle_chunks.C28
public import upper.certificate.NativeCircleData

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Pointers.FastCircles

noncomputable def tree : EncodedCircleTree := (.branch 7168 (.branch 3584 (.branch 1536 (.branch 512 EncodedCircles00.tree (.branch 512 EncodedCircles01.tree EncodedCircles02.tree)) (.branch 1024 (.branch 512 EncodedCircles03.tree EncodedCircles04.tree) (.branch 512 EncodedCircles05.tree EncodedCircles06.tree))) (.branch 1536 (.branch 512 EncodedCircles07.tree (.branch 512 EncodedCircles08.tree EncodedCircles09.tree)) (.branch 1024 (.branch 512 EncodedCircles10.tree EncodedCircles11.tree) (.branch 512 EncodedCircles12.tree EncodedCircles13.tree)))) (.branch 3584 (.branch 1536 (.branch 512 EncodedCircles14.tree (.branch 512 EncodedCircles15.tree EncodedCircles16.tree)) (.branch 1024 (.branch 512 EncodedCircles17.tree EncodedCircles18.tree) (.branch 512 EncodedCircles19.tree EncodedCircles20.tree))) (.branch 2048 (.branch 1024 (.branch 512 EncodedCircles21.tree EncodedCircles22.tree) (.branch 512 EncodedCircles23.tree EncodedCircles24.tree)) (.branch 1024 (.branch 512 EncodedCircles25.tree EncodedCircles26.tree) (.branch 512 EncodedCircles27.tree EncodedCircles28.tree)))))

/-- Reassemble the checked encoded chunks before applying the decoder.
The proof rewrites symbolic lists, never all 14774 decoded circles. -/
theorem flatten_eq : tree.flatten.map Certificate.decodeCircle =
    Certificate.NativeCircleData.circles := by
  simp only [tree, EncodedCircleTree.flatten, EncodedCircles00.flatten_eq,
    EncodedCircles01.flatten_eq,
    EncodedCircles02.flatten_eq,
    EncodedCircles03.flatten_eq,
    EncodedCircles04.flatten_eq,
    EncodedCircles05.flatten_eq,
    EncodedCircles06.flatten_eq,
    EncodedCircles07.flatten_eq,
    EncodedCircles08.flatten_eq,
    EncodedCircles09.flatten_eq,
    EncodedCircles10.flatten_eq,
    EncodedCircles11.flatten_eq,
    EncodedCircles12.flatten_eq,
    EncodedCircles13.flatten_eq,
    EncodedCircles14.flatten_eq,
    EncodedCircles15.flatten_eq,
    EncodedCircles16.flatten_eq,
    EncodedCircles17.flatten_eq,
    EncodedCircles18.flatten_eq,
    EncodedCircles19.flatten_eq,
    EncodedCircles20.flatten_eq,
    EncodedCircles21.flatten_eq,
    EncodedCircles22.flatten_eq,
    EncodedCircles23.flatten_eq,
    EncodedCircles24.flatten_eq,
    EncodedCircles25.flatten_eq,
    EncodedCircles26.flatten_eq,
    EncodedCircles27.flatten_eq,
    EncodedCircles28.flatten_eq,
    List.map_append, Certificate.NativeCircleData.circles,
    Certificate.NativeCircleData.chunks, Certificate.NativeCircles00.circles,
    Certificate.NativeCircles01.circles,
    Certificate.NativeCircles02.circles,
    Certificate.NativeCircles03.circles,
    Certificate.NativeCircles04.circles,
    Certificate.NativeCircles05.circles,
    Certificate.NativeCircles06.circles,
    Certificate.NativeCircles07.circles,
    Certificate.NativeCircles08.circles,
    Certificate.NativeCircles09.circles,
    Certificate.NativeCircles10.circles,
    Certificate.NativeCircles11.circles,
    Certificate.NativeCircles12.circles,
    Certificate.NativeCircles13.circles,
    Certificate.NativeCircles14.circles,
    Certificate.NativeCircles15.circles,
    Certificate.NativeCircles16.circles,
    Certificate.NativeCircles17.circles,
    Certificate.NativeCircles18.circles,
    Certificate.NativeCircles19.circles,
    Certificate.NativeCircles20.circles,
    Certificate.NativeCircles21.circles,
    Certificate.NativeCircles22.circles,
    Certificate.NativeCircles23.circles,
    Certificate.NativeCircles24.circles,
    Certificate.NativeCircles25.circles,
    Certificate.NativeCircles26.circles,
    Certificate.NativeCircles27.circles,
    Certificate.NativeCircles28.circles,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

noncomputable def circleAt (i : Nat) : List Nat :=
  Certificate.decodeCircle (tree.get i)

theorem circleAt_mem (i : Nat) (_hi : i < 14774) :
    circleAt i ∈ Certificate.NativeCircleData.circles := by
  rw [← flatten_eq]
  exact tree.decode_get_mem i

end SuperpermutationUpperBound.Native14.Pointers.FastCircles
