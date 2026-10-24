module

public import upper.pointers.Trace
public import upper.certificate.SourcePrefixes

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Pointers
open Transport SeedFamily Certificate

/-- A balanced lookup representation. Cached branch sizes guide lookup, but
semantic soundness needs only that every returned point is an actual leaf. -/
inductive PointTree where
  | leaf (points : List Point)
  | branch (leftSize : Nat) (left right : PointTree)

namespace PointTree

def flatten : PointTree→List Point
  | .leaf points=>points
  | .branch _ left right=>left.flatten++right.flatten

def get? : PointTree→Nat→Option Point
  | .leaf points,i=>points[i]?
  | .branch leftSize left right,i=>
      if i<leftSize then left.get? i else right.get? (i-leftSize)

theorem get_mem {tree : PointTree} {i : Nat} {p : Point}
    (hp : tree.get? i=some p) : p∈tree.flatten := by
  induction tree generalizing i with
  | leaf points =>
      obtain ⟨hi,he⟩ := List.getElem?_eq_some_iff.mp hp
      exact he ▸ List.getElem_mem hi
  | branch size left right ihl ihr =>
      simp only [get?] at hp
      split at hp
      · exact List.mem_append_left _ (ihl hp)
      · exact List.mem_append_right _ (ihr hp)

/-- A leaf point is an actual occurrence when the row and ledger projections
are the checked source lists. These equalities are proved once per source. -/
theorem point_mem_sound (points : List Point) (rows : List (Row Nat)) (prefixes : List Int)
    (hrows : points.map Point.row=rows) (hexcess : points.map Point.excess=prefixes)
    (hcheck : sourcePrefixCheck rows prefixes 0=true) (p : Point) (hp : p∈points) :
    p.Occurs rows := by
  subst rows
  subst prefixes
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hp
  have hmi : i<(points.map Point.row).length := by simpa using hi
  have ho := sourcePrefix_occurrence hcheck i hmi
  have hexc : (points.map Point.excess).getD i 0=points[i].excess := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using hi)]
    simp only [List.getElem_map,Option.getD_some]
  simpa only [Point.Occurs,RowOccurrence,List.getElem_map,hexc,he] using ho

theorem get_sound (tree : PointTree) (rows : List (Row Nat)) (prefixes : List Int)
    (hrows : tree.flatten.map Point.row=rows) (hexcess : tree.flatten.map Point.excess=prefixes)
    (hcheck : sourcePrefixCheck rows prefixes 0=true) (i : Nat) {p : Point}
    (hp : tree.get? i=some p) : p.Occurs rows :=
  point_mem_sound tree.flatten rows prefixes hrows hexcess hcheck p (get_mem hp)

end PointTree
end SuperpermutationUpperBound.Native14.Pointers
