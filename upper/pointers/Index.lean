module

public import upper.seed_family.Membership

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Pointers
open CircleTransport Transport SeedFamily Certificate
open SuperpermutationUpperBound.Partition

def p7 (i : Nat) : Fin 7 := ⟨i/720%7,Nat.mod_lt _ (by decide)⟩
def p8 (i : Nat) : Fin 8 := ⟨i/90%8,Nat.mod_lt _ (by decide)⟩
def p9 (i : Nat) : Fin 9 := ⟨i/10%9,Nat.mod_lt _ (by decide)⟩
def p10 (i : Nat) : Fin 10 := ⟨i%10,Nat.mod_lt _ (by decide)⟩
def blockIndex (i : Nat) : Fin 22 := ⟨(i-10080)%22,Nat.mod_lt _ (by decide)⟩
noncomputable def ancestor (i : Nat) : List Nat :=
  EmptyLoops.halfarAncestors.getD ((i-10080)/22) []

/-- The 10080 outside parents followed by the 48 families of 22 mixed parents.
Ordinary full-chart parents have their separate uniform connector proof. -/
noncomputable def parentAt (i : Nat) : List (Row Nat) :=
  if i < 10080 then outsideAt (decide (5040 ≤ i)) (p7 i) (p8 i) (p9 i) (p10 i)
  else (mixedAt (blockIndex i)).map (Row.map (Partition.relabelSeven (ancestor i)))

def outsideIndex (b : Bool) (a : Fin 7) (c : Fin 8) (d : Fin 9) (e : Fin 10) : Nat :=
  (if b then 5040 else 0)+720*a.val+90*c.val+10*d.val+e.val

theorem outsideIndex_lt (b : Bool) (a : Fin 7) (c : Fin 8) (d : Fin 9) (e : Fin 10) :
    outsideIndex b a c d e < 10080 := by
  cases b <;> simp only [outsideIndex,Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem parentAt_outside (b : Bool) (a : Fin 7) (c : Fin 8) (d : Fin 9) (e : Fin 10) :
    parentAt (outsideIndex b a c d e) = outsideAt b a c d e := by
  rw [parentAt,if_pos (outsideIndex_lt b a c d e)]
  have hb : decide (5040≤outsideIndex b a c d e)=b := by
    cases b <;> simp only [outsideIndex,Bool.false_eq_true,ite_false,ite_true]
    · exact decide_eq_false (by omega)
    · exact decide_eq_true (by omega)
  rw [hb]
  have h7 : p7 (outsideIndex b a c d e)=a := by
    apply Fin.ext
    cases b <;> simp only [p7,outsideIndex,Bool.false_eq_true,ite_false,ite_true]
      <;> omega
  have h8 : p8 (outsideIndex b a c d e)=c := by
    apply Fin.ext
    cases b <;> simp only [p8,outsideIndex,Bool.false_eq_true,ite_false,ite_true]
      <;> omega
  have h9 : p9 (outsideIndex b a c d e)=d := by
    apply Fin.ext
    cases b <;> simp only [p9,outsideIndex,Bool.false_eq_true,ite_false,ite_true]
      <;> omega
  have h10 : p10 (outsideIndex b a c d e)=e := by
    apply Fin.ext
    cases b <;> simp only [p10,outsideIndex,Bool.false_eq_true,ite_false,ite_true]
      <;> omega
  rw [h7,h8,h9,h10]

theorem parentAt_block (a : Nat) (x : List Nat)
    (hx : EmptyLoops.halfarAncestors[a]?=some x) (j : Fin 22) :
    parentAt (10080+22*a+j.val) = (mixedAt j).map (Row.map (Partition.relabelSeven x)) := by
  rw [parentAt,if_neg (by omega)]
  have hj : blockIndex (10080+22*a+j.val)=j := by
    apply Fin.ext
    simp only [blockIndex]
    omega
  have ha : ancestor (10080+22*a+j.val)=x := by
    simp only [ancestor,show (10080+22*a+j.val-10080)/22=a by omega,
      List.getD_eq_getElem?_getD,hx,Option.getD_some]
  rw [hj,ha]

theorem family_cases_index (i : SeedFamily.Index) :
    (∃k<11136, family i=parentAt k) ∨
    (∃x∈EmptyLoops.halfarAncestors,∃y∈EmptyLoops.blockFEmpty,
      family i=(fullChart y 11 12).map (Row.map (Partition.relabelSeven x))) := by
  rcases family_cases i with ⟨b,a,c,d,e,he⟩ | ⟨x,hx,j,he⟩ | ho
  · exact Or.inl ⟨outsideIndex b a c d e,by have := outsideIndex_lt b a c d e;omega,
      he.trans (parentAt_outside b a c d e).symm⟩
  · obtain ⟨a,ha,hax⟩ := List.mem_iff_getElem.mp hx
    have hal : a<48 := by simpa only [EmptyLoops.halfarAncestors_length] using ha
    have hget : EmptyLoops.halfarAncestors[a]?=some x :=
      List.getElem?_eq_some_iff.mpr ⟨ha,hax⟩
    exact Or.inl ⟨10080+22*a+j.val,by omega,he.trans (parentAt_block a x hget j).symm⟩
  · exact Or.inr ho

end SuperpermutationUpperBound.Native14.Pointers
