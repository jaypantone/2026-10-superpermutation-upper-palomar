module

public import upper.seed_family.Native

@[expose] public section

namespace SuperpermutationUpperBound.Native14.SeedFamily
open CircleTransport Transport
open SuperpermutationUpperBound.Partition
open Certificate

def outsideSource : Bool→List (Row Nat)
  | false => Halfar0.rows
  | true => Halfar1.rows

/-- Source indices used by the small inverse-pointer certificate. -/
def outsideAt (b : Bool) (p7 : Fin 7) (p8 : Fin 8) (p9 : Fin 9) (p10 : Fin 10) : List (Row Nat) :=
  transportWalk (transportWalk (transportWalk (transportWalk (outsideSource b) 8 p7.val)
    9 p8.val) 10 p9.val) 11 p10.val

theorem outside_cases {t : List (Row Nat)} (ht : t∈outsideFamilies) :
    ∃b p7 p8 p9 p10,t=outsideAt b p7 p8 p9 p10 := by
  obtain ⟨r3,hr3,p10,rfl⟩ := mem_step ht
  obtain ⟨r2,hr2,p9,rfl⟩ := mem_step hr3
  obtain ⟨r1,hr1,p8,rfl⟩ := mem_step hr2
  obtain ⟨r0,hr0,p7,rfl⟩ := mem_step hr1
  have hs : r0=Halfar0.rows ∨ r0=Halfar1.rows := by simpa [iterate,sourceFamilies] using hr0
  rcases hs with rfl | rfl
  · exact ⟨false,p7,p8,p9,p10,rfl⟩
  · exact ⟨true,p7,p8,p9,p10,rfl⟩

/-- The 22 exceptional local parent trails, before ancestor relabeling. -/
def mixedAt (i : Fin 22) : List (Row Nat) :=
  if i.val<2 then transportWalk (Regularization.repeatRows BlockF0.rows 5) 11 i.val
  else if i.val<12 then transportWalk BlockF1.rows 11 (i.val-2)
  else transportWalk BlockF2.rows 11 (i.val-12)

theorem local_cases {t : List (Row Nat)} (ht : t∈localFamilies) :
    (∃i:Fin 22,t=mixedAt i) ∨
      ∃x∈EmptyLoops.blockFEmpty,t=fullChart x 11 12 := by
  rcases List.mem_append.mp ht with ht | ht
  · rcases List.mem_append.mp ht with ht | ht
    · have hs : t=transportWalk (Regularization.repeatRows BlockF0.rows 5) 11 0 ∨
          t=transportWalk (Regularization.repeatRows BlockF0.rows 5) 11 1 := by
        simpa [Regularization.BlockF0.tracks,Regularization.fiveTracks] using ht
      rcases hs with rfl | rfl
      · exact Or.inl ⟨⟨0,by decide⟩,rfl⟩
      · exact Or.inl ⟨⟨1,by decide⟩,rfl⟩
    · obtain ⟨rs,hrs,p,rfl⟩ := mem_step ht
      have hs : rs=BlockF1.rows ∨ rs=BlockF2.rows := by simpa [blockSimpleSources] using hrs
      rcases hs with rfl | rfl
      · refine Or.inl ⟨⟨p.val+2,by omega⟩,?_⟩
        simp [mixedAt,show ¬p.val+2<2 by omega,show p.val+2<12 by omega]
      · refine Or.inl ⟨⟨p.val+12,by omega⟩,?_⟩
        simp [mixedAt,show ¬p.val+12<2 by omega,show ¬p.val+12<12 by omega]
  · obtain ⟨x,hx,he⟩ := List.mem_map.mp ht
    exact Or.inr ⟨x,hx,he.symm⟩

/-- Decompose an arbitrary actual parent without expanding its rows or its
position in the 57504-member family. -/
theorem native_cases {t : List (Row Nat)} (ht : t∈nativeFamilies) :
    (∃b p7 p8 p9 p10,t=outsideAt b p7 p8 p9 p10) ∨
    (∃x∈EmptyLoops.halfarAncestors,∃i:Fin 22,
      t=(mixedAt i).map (Row.map (Partition.relabelSeven x))) ∨
    (∃x∈EmptyLoops.halfarAncestors,∃y∈EmptyLoops.blockFEmpty,
      t=(fullChart y 11 12).map (Row.map (Partition.relabelSeven x))) := by
  rcases List.mem_append.mp ht with ht | ht
  · exact Or.inl (outside_cases ht)
  · obtain ⟨x,hx,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨rs,hrs,rfl⟩ := List.mem_map.mp ht
    rcases local_cases hrs with ⟨i,rfl⟩ | ⟨y,hy,rfl⟩
    · exact Or.inr (Or.inl ⟨x,hx,i,rfl⟩)
    · exact Or.inr (Or.inr ⟨x,hx,y,hy,rfl⟩)

/-- The same structural elimination at the actual base-label interface. -/
theorem family_cases (i : Index) :
    (∃b p7 p8 p9 p10,family i=outsideAt b p7 p8 p9 p10) ∨
    (∃x∈EmptyLoops.halfarAncestors,∃j:Fin 22,
      family i=(mixedAt j).map (Row.map (Partition.relabelSeven x))) ∨
    (∃x∈EmptyLoops.halfarAncestors,∃y∈EmptyLoops.blockFEmpty,
      family i=(fullChart y 11 12).map (Row.map (Partition.relabelSeven x))) :=
  native_cases (List.getElem_mem i.isLt)

end SuperpermutationUpperBound.Native14.SeedFamily
