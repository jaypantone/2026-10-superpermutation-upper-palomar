module

public import SuperpermutationUpperBound.Partition.Basic
public import SuperpermutationUpperBound.Partition.FullCharts
public import SuperpermutationUpperBound.Foundation.RowRelabeling

@[expose] public section

/-! Semantic replacement of cyclic row blocks. These lemmas preserve actual
coverage and do not infer it from row counts or charges. -/
namespace SuperpermutationUpperBound.Native14.Partition
open SuperpermutationUpperBound.Partition

variable {α β : Type}

/-- Every source row's cyclic base is represented in the target row list. -/
def BlockRefines (rs ts : List (Row α)) : Prop :=
  ∀ r ∈ rs, ∃ t ∈ ts, CyclicEq t.base r.base

theorem row_base_nonempty {r : Row α} (hr : r.Valid) : r.base ≠ [] := by
  have hn := hr.2.2.1
  have hm := hr.2.2.2
  intro he
  rw [he, List.length_nil] at hm
  omega

theorem BlockRefines.refl {rs : List (Row α)}
    (hv : ∀ r ∈ rs, r.Valid) : BlockRefines rs rs := by
  intro r hr
  exact ⟨r, hr, CyclicEq.refl (row_base_nonempty (hv r hr))⟩

theorem BlockRefines.trans {rs ts us : List (Row α)}
    (h₁ : BlockRefines rs ts) (h₂ : BlockRefines ts us) : BlockRefines rs us := by
  intro r hr
  obtain ⟨t, ht, htr⟩ := h₁ r hr
  obtain ⟨u, hu, hut⟩ := h₂ t ht
  exact ⟨u, hu, hut.trans htr⟩

theorem BlockRefines.append {rs rs' ts ts' : List (Row α)}
    (h : BlockRefines rs ts) (h' : BlockRefines rs' ts') :
    BlockRefines (rs ++ rs') (ts ++ ts') := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨t, ht, hc⟩ := h r hr
    exact ⟨t, List.mem_append.mpr (Or.inl ht), hc⟩
  · obtain ⟨t, ht, hc⟩ := h' r hr
    exact ⟨t, List.mem_append.mpr (Or.inr ht), hc⟩

theorem BlockRefines.flatMap {ι : Type} (is : List ι) {f g : ι → List (Row α)}
    (h : ∀ i ∈ is, BlockRefines (f i) (g i)) :
    BlockRefines (is.flatMap f) (is.flatMap g) := by
  intro r hr
  obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨t, ht, hc⟩ := h i hi r hr
  exact ⟨t, List.mem_flatMap.mpr ⟨i, hi, ht⟩, hc⟩

theorem BlockRefines.complete {rs ts : List (Row α)} {alphabet : List α}
    (h : BlockRefines rs ts) (hc : BlockComplete alphabet rs) :
    BlockComplete alphabet ts := by
  intro x hx
  obtain ⟨r, hr, hrc⟩ := hc x hx
  obtain ⟨t, ht, htr⟩ := h r hr
  exact ⟨t, ht, htr.trans hrc⟩

/-- Replacement commutes with transport, including the exceptional short row. -/
theorem BlockRefines.transport {rs ts : List (Row α)}
    (h : BlockRefines rs ts) (hr : ∀ r ∈ rs, r.Valid)
    (ht : ∀ t ∈ ts, t.Valid) (z : α) :
    BlockRefines (Transport.packingRows rs z) (Transport.packingRows ts z) := by
  intro r' hr'
  obtain ⟨r, hrmem, hrr'⟩ := List.mem_flatMap.mp hr'
  obtain ⟨t, htmem, htr⟩ := h r hrmem
  have hb := Transport.rows_base_inInsertionBlock (hr r hrmem) hrr'
  have hbt : InInsertionBlock z t.base r'.base := (InInsertionBlock.congr_base htr).mpr hb
  obtain ⟨t', htt', hc⟩ :=
    (Transport.rows_cyclicEq_iff_inInsertionBlock (ht t htmem) z r'.base).mpr hbt
  exact ⟨t', List.mem_flatMap.mpr ⟨t, htmem, htt'⟩, hc⟩

theorem CyclicEq.map {x y : List α} (h : CyclicEq x y) (f : α → β) :
    CyclicEq (x.map f) (y.map f) := by
  obtain ⟨j, hj⟩ := h
  refine ⟨⟨j.val, by simpa using j.isLt⟩, ?_⟩
  simpa only [rot_map] using congrArg (List.map f) hj

theorem BlockRefines.map {rs ts : List (Row α)} (h : BlockRefines rs ts)
    (f : α → β) : BlockRefines (rs.map (Row.map f)) (ts.map (Row.map f)) := by
  intro r hr
  obtain ⟨q, hq, hqr⟩ := List.mem_map.mp hr
  subst r
  obtain ⟨t, ht, hc⟩ := h q hq
  exact ⟨t.map f, List.mem_map_of_mem ht, CyclicEq.map hc f⟩

/-- Full charts cover exactly the descendants of a full accounting row. -/
theorem fullChart_refines_transport (x : List α) (z s : α)
    (hv : (Row.mk x s x.length).Valid) :
    BlockRefines (Transport.rows (Row.mk x s x.length) z) (fullChart x z s) := by
  intro r hr
  have hb := Transport.rows_base_inInsertionBlock hv hr
  exact (fullChart_cyclicEq_iff_inInsertionBlock x r.base z s).mpr hb

theorem transport_refines_fullChart (x : List α) (z s : α)
    (hv : (Row.mk x s x.length).Valid) :
    BlockRefines (fullChart x z s) (Transport.rows (Row.mk x s x.length) z) := by
  intro r hr
  have hn : r.base ≠ [] := by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    simp [fullChartAt]
  have hb := (fullChart_cyclicEq_iff_inInsertionBlock x r.base z s).mp
    ⟨r, hr, CyclicEq.refl hn⟩
  exact (Transport.rows_cyclicEq_iff_inInsertionBlock hv z r.base).mpr hb

/-- Replacing empty full accounting rows by literal closed charts preserves all
cyclic blocks after the last fresh letter is inserted. -/
theorem filledCharts_refines_transport (selected : List (Row α))
    (empty : List (List α)) (z s : α)
    (hs : ∀ r ∈ selected, r.Valid)
    (he : ∀ x ∈ empty, (Row.mk x s x.length).Valid) :
    BlockRefines
      (Transport.packingRows (selected ++ empty.map (fun x => Row.mk x s x.length)) z)
      (Transport.packingRows selected z ++ empty.flatMap (fun x => fullChart x z s)) := by
  intro r hr
  obtain ⟨q, hq, hqr⟩ := List.mem_flatMap.mp hr
  rcases List.mem_append.mp hq with hq | hq
  · exact ⟨r, List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨q,hq,hqr⟩)),
      CyclicEq.refl (Transport.rows_base_nonempty hqr)⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    obtain ⟨t, ht, hc⟩ := fullChart_refines_transport x z s (he x hx) r hqr
    exact ⟨t, List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨x,hx,ht⟩)), hc⟩

end SuperpermutationUpperBound.Native14.Partition
