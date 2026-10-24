module

public import upper.certificate.empty_parts.Halfar
public import upper.certificate.empty_parts.Ancestors
public import upper.certificate.empty_parts.BlockF00
public import upper.certificate.empty_parts.BlockF01

public import SuperpermutationUpperBound.Certificates.NineRecipeData

@[expose] public section

/-! The original ordered omitted-loop lists, checked in bounded literal pieces.
All public lists and claims retain their original meanings. -/
namespace SuperpermutationUpperBound.Native14.Certificate.EmptyLoops
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def halfarEmptyEncoded : List String :=
  EmptyLoopParts.Halfar.encoded

def halfarEmpty : List (List Nat) := halfarEmptyEncoded.map (fun x => x.toList.map decodeLetter)

theorem halfarEmpty_blocks : halfarEmpty =
  EmptyLoopParts.Halfar.bases := by
  simp only [halfarEmpty, halfarEmptyEncoded, List.map_append, EmptyLoopParts.Halfar.bases]

theorem halfarEmpty_length : halfarEmpty.length = 336 := by
  simp only [halfarEmpty, List.length_map, halfarEmptyEncoded, List.length_append, EmptyLoopParts.Halfar.encoded_length, Nat.reduceAdd]

theorem halfarEmpty_perm : ∀ x ∈ halfarEmpty, x.Perm (List.range 8) := by
  have hh : halfarEmpty.all (fun x => decide (x.Perm (List.range 8))) = true := by
    simp only [halfarEmpty_blocks, List.all_append, EmptyLoopParts.Halfar.checked, Bool.and_self]
  intro x hx
  exact of_decide_eq_true ((List.all_eq_true.mp hh) x hx)

def halfarAncestorsEncoded : List String :=
  EmptyLoopParts.Ancestors.encoded

def halfarAncestors : List (List Nat) := halfarAncestorsEncoded.map (fun x => x.toList.map decodeLetter)

theorem halfarAncestors_blocks : halfarAncestors =
  EmptyLoopParts.Ancestors.bases := by
  simp only [halfarAncestors, halfarAncestorsEncoded, List.map_append, EmptyLoopParts.Ancestors.bases]

theorem halfarAncestors_length : halfarAncestors.length = 48 := by
  simp only [halfarAncestors, List.length_map, halfarAncestorsEncoded, List.length_append, EmptyLoopParts.Ancestors.encoded_length, Nat.reduceAdd]

theorem halfarAncestors_perm : ∀ x ∈ halfarAncestors, x.Perm (List.range 7) := by
  have hh : halfarAncestors.all (fun x => decide (x.Perm (List.range 7))) = true := by
    simp only [halfarAncestors_blocks, List.all_append, EmptyLoopParts.Ancestors.checked, Bool.and_self]
  intro x hx
  exact of_decide_eq_true ((List.all_eq_true.mp hh) x hx)

def blockFEmptyEncoded : List String :=
  EmptyLoopParts.BlockF00.encoded ++
  EmptyLoopParts.BlockF01.encoded

def blockFEmpty : List (List Nat) := blockFEmptyEncoded.map (fun x => x.toList.map decodeLetter)

theorem blockFEmpty_blocks : blockFEmpty =
  EmptyLoopParts.BlockF00.bases ++
  EmptyLoopParts.BlockF01.bases := by
  simp only [blockFEmpty, blockFEmptyEncoded, List.map_append, EmptyLoopParts.BlockF00.bases, EmptyLoopParts.BlockF01.bases]

theorem blockFEmpty_length : blockFEmpty.length = 966 := by
  simp only [blockFEmpty, List.length_map, blockFEmptyEncoded, List.length_append, EmptyLoopParts.BlockF00.encoded_length, EmptyLoopParts.BlockF01.encoded_length, Nat.reduceAdd]

theorem blockFEmpty_perm : ∀ x ∈ blockFEmpty, x.Perm (List.range 11) := by
  have hh : blockFEmpty.all (fun x => decide (x.Perm (List.range 11))) = true := by
    simp only [blockFEmpty_blocks, List.all_append, EmptyLoopParts.BlockF00.checked, EmptyLoopParts.BlockF01.checked, Bool.and_self]
  intro x hx
  exact of_decide_eq_true ((List.all_eq_true.mp hh) x hx)

theorem halfarAncestors_eq_historical :
    halfarAncestors = Certificates.NineRecipe.unusedBases := by decide

end SuperpermutationUpperBound.Native14.Certificate.EmptyLoops
