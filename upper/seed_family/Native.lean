module

public import upper.seed_family.Iteration
public import upper.seed_family.Relabel
public import upper.regularization.BlockF0
public import upper.partition.NativeRows

@[expose] public section

namespace SuperpermutationUpperBound.Native14.SeedFamily
open CircleTransport Transport
open SuperpermutationUpperBound.Partition
open Certificate

theorem shape_of_basedOn_range {n s : Nat} {rs : List (Row Nat)}
    (hb : BasedOn (List.range n) s rs) : Shape n rs := by
  intro r hr
  have hh := hb r hr
  exact ⟨by simpa using hh.2.1.length_eq,hh.2.2.2⟩

def sourceFamilies : List (List (Row Nat)) := [Halfar0.rows,Halfar1.rows]

theorem source_regular : Regular 7 sourceFamilies := by
  intro rs hrs
  have hs : rs=Halfar0.rows ∨ rs=Halfar1.rows := by simpa [sourceFamilies] using hrs
  rcases hs with rfl | rfl
  · exact ⟨Halfar0.rows_closed,by rw [Halfar0.rows_excess];decide,
      shape_of_basedOn_range Halfar0.rows_basedOn⟩
  · exact ⟨Halfar1.rows_closed,by rw [Halfar1.rows_excess];decide,
      shape_of_basedOn_range Halfar1.rows_basedOn⟩

def outsideFamilies : List (List (Row Nat)) := iterate 7 sourceFamilies 4

theorem outside_regular : Regular 11 outsideFamilies := iterate_regular 7 (by decide) source_regular 4

theorem outside_inventory : outsideFamilies.flatten.Perm (Partition.extendRange Partition.seedRows 8 4) := by
  simpa only [outsideFamilies,sourceFamilies,List.flatten_cons,List.flatten_nil,List.append_nil,
    Partition.seedRows] using iterate_inventory 7 (by decide) source_regular 4

theorem outside_length : outsideFamilies.length=10080 := by
  simp only [outsideFamilies,iterate,step_length,sourceFamilies,List.length_cons,List.length_nil]

def blockSimpleSources : List (List (Row Nat)) := [BlockF1.rows,BlockF2.rows]

theorem blockSimple_regular : Regular 10 blockSimpleSources := by
  intro rs hrs
  have hs : rs=BlockF1.rows ∨ rs=BlockF2.rows := by simpa [blockSimpleSources] using hrs
  rcases hs with rfl | rfl
  · exact ⟨BlockF1.rows_closed,by rw [BlockF1.rows_excess];decide,
      shape_of_basedOn_range BlockF1.rows_basedOn⟩
  · exact ⟨BlockF2.rows_closed,by rw [BlockF2.rows_excess];decide,
      shape_of_basedOn_range BlockF2.rows_basedOn⟩

def emptyFamilies : List (List (Row Nat)) := EmptyLoops.blockFEmpty.map (fun x=>fullChart x 11 12)

theorem empty_regular : Regular 11 emptyFamilies := by
  intro rs hrs
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hrs
  have hl : x.length=11 := by simpa using (EmptyLoops.blockFEmpty_perm x hx).length_eq
  refine ⟨fullChart_closedTrail x 11 12 (by omega), ?_, ?_⟩
  · simp only [signedExcess,fullChart_length,fullChart_charge_sum,hl]
    decide
  · intro r hr
    have hb := fullChart_base_length x 11 12 r hr
    have hf := fullChart_visible x 11 12 r hr
    exact ⟨by omega,Or.inl (hf.trans hb.symm)⟩

def localFamilies : List (List (Row Nat)) :=
  Regularization.BlockF0.tracks ++ step 10 11 blockSimpleSources ++ emptyFamilies

theorem local_regular : Regular 11 localFamilies := by
  apply regular_append
  · apply regular_append
    · intro rs hrs
      have hc := Regularization.BlockF0.tracks_closed_regular rs hrs
      exact ⟨hc.1,hc.2,shape_of_basedOn_range (Regularization.BlockF0.tracks_basedOn rs hrs)⟩
    · exact step_regular 10 (by decide) 11 blockSimple_regular
  · exact empty_regular

theorem local_inventory : localFamilies.flatten.Perm Partition.localRows := by
  have hs := step_inventory 10 (by decide) 11 blockSimpleSources
    (fun rs hrs r hr => ((blockSimple_regular rs hrs).2.2 r hr).1)
  have hh := (Regularization.BlockF0.tracks_inventory.append hs).append
    (List.Perm.refl emptyFamilies.flatten)
  simpa only [localFamilies,blockSimpleSources,emptyFamilies,Partition.localRows,Partition.blockRows,
    List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil,
    ←List.flatMap_def,Transport.packingRows,List.flatMap_append,List.append_assoc] using hh

theorem local_length : localFamilies.length=988 := by
  simp only [localFamilies,List.length_append,Regularization.BlockF0.tracks_length,step_length,
    blockSimpleSources,List.length_cons,List.length_nil,emptyFamilies,List.length_map,
    EmptyLoops.blockFEmpty_length]

def nativeFamilies : List (List (Row Nat)) :=
  outsideFamilies ++ EmptyLoops.halfarAncestors.flatMap
    (fun x=>relabel (Partition.relabelSeven x) localFamilies)

theorem native_regular : Regular 11 nativeFamilies := by
  exact regular_append outside_regular (regular_flatMap _ _
    (fun x _ => relabel_regular (Partition.relabelSeven x) local_regular))

theorem native_inventory : nativeFamilies.flatten.Perm Partition.nativeRows := by
  have ha : (EmptyLoops.halfarAncestors.flatMap
      (fun x=>relabel (Partition.relabelSeven x) localFamilies)).flatten.Perm
      (EmptyLoops.halfarAncestors.flatMap (fun x=>Partition.localRows.map (Row.map (Partition.relabelSeven x)))) := by
    generalize EmptyLoops.halfarAncestors=xs
    induction xs with
    | nil => exact List.Perm.refl _
    | cons x xs ih =>
        simp only [List.flatMap_cons,List.flatten_append,relabel_inventory]
        exact (local_inventory.map (Row.map (Partition.relabelSeven x))).append ih
  unfold nativeFamilies Partition.nativeRows
  rw [List.flatten_append]
  exact outside_inventory.append ha

theorem native_length : nativeFamilies.length=57504 := by
  simp only [nativeFamilies,List.length_append,outside_length,List.length_flatMap,
    relabel_length,local_length,List.map_const',List.sum_replicate,EmptyLoops.halfarAncestors_length]
  decide

abbrev Index := Fin nativeFamilies.length

def labels : List Index := List.finRange nativeFamilies.length

def family (i : Index) : List (Row Nat) := nativeFamilies[i.val]

theorem labels_complete (i : Index) : i∈labels := List.mem_finRange i

theorem labels_nodup : labels.Nodup := List.nodup_finRange _

theorem labels_length : labels.length=57504 := by simpa [labels] using native_length

theorem family_inventory : (labels.flatMap family).Perm Partition.nativeRows := by
  have hh : labels.map family=nativeFamilies := finRange_enumeration nativeFamilies
  rw [List.flatMap_def,hh]
  exact native_inventory

theorem family_closed (i : Index) : ClosedTrail (family i) :=
  (native_regular _ (List.getElem_mem i.isLt)).1

theorem family_winding (i : Index) : (11:Int) ∣ signedExcess (family i) :=
  (native_regular _ (List.getElem_mem i.isLt)).2.1

theorem family_shape (i : Index) : Shape 12 (family i) :=
  (native_regular _ (List.getElem_mem i.isLt)).2.2

end SuperpermutationUpperBound.Native14.SeedFamily
