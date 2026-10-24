module

public import upper.seed_family.Lift
public import SuperpermutationUpperBound.Foundation.RowRelabeling

@[expose] public section

namespace SuperpermutationUpperBound.Native14.SeedFamily
open CircleTransport Transport
variable {α β : Type}

def relabel (f : α→β) (families : List (List (Row α))) : List (List (Row β)) :=
  families.map (fun rs => rs.map (Row.map f))

theorem signedExcess_map (f : α→β) (rs : List (Row α)) :
    signedExcess (rs.map (Row.map f))=signedExcess rs := by
  simp only [signedExcess,List.length_map,List.map_map,Function.comp_def,Row.map_charge]

theorem relabel_regular (f : α→β) {h : Nat} {families : List (List (Row α))}
    (hr : Regular h families) : Regular h (relabel f families) := by
  intro ts ht
  obtain ⟨rs,hrs,rfl⟩ := List.mem_map.mp ht
  have hh := hr rs hrs
  refine ⟨closedTrail_map f hh.1, ?_, ?_⟩
  · simpa only [signedExcess_map] using hh.2.1
  · intro r hr
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    simpa only [Row.map_base_length,Row.map_visible] using hh.2.2 s hs

theorem relabel_inventory (f : α→β) (families : List (List (Row α))) :
    (relabel f families).flatten=families.flatten.map (Row.map f) := by
  exact List.map_flatten.symm

@[simp] theorem relabel_length (f : α→β) (families : List (List (Row α))) :
    (relabel f families).length=families.length := by simp [relabel]

theorem regular_append {h : Nat} {xs ys : List (List (Row α))}
    (hx : Regular h xs) (hy : Regular h ys) : Regular h (xs++ys) := by
  intro rs hr
  exact (List.mem_append.mp hr).elim (hx rs) (hy rs)

theorem regular_flatMap {ι : Type} {h : Nat} (labels : List ι)
    (families : ι→List (List (Row α)))
    (hr : ∀i∈labels,Regular h (families i)) : Regular h (labels.flatMap families) := by
  intro rs hrs
  obtain ⟨i,hi,hrsi⟩ := List.mem_flatMap.mp hrs
  exact hr i hi rs hrsi

end SuperpermutationUpperBound.Native14.SeedFamily
