module

public import upper.partition.Blocks

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Partition
open SuperpermutationUpperBound.Partition

variable {α β : Type}

theorem basedOn_map {alphabet : List α} {s : α} {rs : List (Row α)}
    (h : BasedOn alphabet s rs) (f : α → β) (hf : Function.Injective f) :
    BasedOn (alphabet.map f) (f s) (rs.map (Row.map f)) := by
  intro r hr
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
  have hq' := h q hq
  refine ⟨Row.map_valid f (fun a b h => hf h) hq'.1, hq'.2.1.map f, ?_, ?_⟩
  · simp only [Row.map_satellite, hq'.2.2.1]
  · simpa only [Row.map_visible, Row.map_base_length] using hq'.2.2.2

theorem insertLetter_map (f : α → β) (x : List α) (z : α) (j : Nat) :
    Transport.insertLetter (x.map f) (f z) j = (Transport.insertLetter x z j).map f := by
  simp [Transport.insertLetter, List.map_append, List.map_take, List.map_drop]

theorem transport_rows_map (f : α → β) (r : Row α) (z : α) :
    Transport.rows (r.map f) (f z) = (Transport.rows r z).map (Row.map f) := by
  simp only [Transport.rows, Row.map_visible, Row.map_base_length]
  split
  · simp [Transport.fullRows, Transport.fullBases, List.map_map,
      Function.comp_def, insertLetter_map, Row.map]
  · simp [Transport.shortRows, Transport.shortBases, List.map_map,
      Function.comp_def, insertLetter_map, Row.map, rot_map]

theorem transport_packingRows_map (f : α → β) (rs : List (Row α)) (z : α) :
    Transport.packingRows (rs.map (Row.map f)) (f z) =
      (Transport.packingRows rs z).map (Row.map f) := by
  simp only [Transport.packingRows, List.flatMap_map, List.map_flatMap,
    transport_rows_map]

theorem fullChart_map (f : α → β) (x : List α) (z s : α) :
    fullChart (x.map f) (f z) (f s) = (fullChart x z s).map (Row.map f) := by
  simp [fullChart, fullChartAt, List.map_map, Row.map, rot_map]

/-- Relabel the original seven letters according to one ancestor cycle. -/
def relabelSeven (x : List Nat) (a : Nat) : Nat :=
  if a < 7 then x[a]?.getD a else a

@[simp] theorem relabelSeven_fixed (x : List Nat) {a : Nat} (ha : 7 ≤ a) :
    relabelSeven x a = a := by simp [relabelSeven, show ¬a<7 by omega]

theorem relabelSeven_injective {x : List Nat} (hx : x.Perm (List.range 7)) :
    Function.Injective (relabelSeven x) := by
  have hl : x.length = 7 := by simpa using hx.length_eq
  have hn : x.Nodup := hx.nodup_iff.mpr List.nodup_range
  have hbound (i : Nat) (hi : i < 7) : x[i]'(by omega) < 7 :=
    List.mem_range.mp (hx.mem_iff.mp (List.getElem_mem (by omega)))
  intro a b he
  by_cases ha : a < 7 <;> by_cases hb : b < 7
  · have he' : x[a]'(by omega) = x[b]'(by omega) := by
      simpa only [relabelSeven, if_pos ha, if_pos hb,
        List.getElem?_eq_getElem (show a<x.length by omega),
        List.getElem?_eq_getElem (show b<x.length by omega), Option.getD_some] using he
    exact (List.getElem_inj hn).mp he'
  · have he' : x[a]'(by omega) = b := by
      simpa only [relabelSeven, if_pos ha, if_neg hb,
        List.getElem?_eq_getElem (show a<x.length by omega), Option.getD_some] using he
    have hh := hbound a ha
    omega
  · have he' : a = x[b]'(by omega) := by
      simpa only [relabelSeven, if_neg ha, if_pos hb,
        List.getElem?_eq_getElem (show b<x.length by omega), Option.getD_some] using he
    have hh := hbound b hb
    omega
  · simpa only [relabelSeven, if_neg ha, if_neg hb] using he

theorem relabelSeven_range {x : List Nat} (hx : x.Perm (List.range 7)) :
    (List.range 7).map (relabelSeven x) = x := by
  have hl : x.length = 7 := by simpa using hx.length_eq
  apply List.ext_getElem
  · simp [hl]
  · intro i hi hi'
    have hi7 : i < 7 := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, relabelSeven, if_pos hi7,
      List.getElem?_eq_getElem hi', Option.getD_some]

end SuperpermutationUpperBound.Native14.Partition
