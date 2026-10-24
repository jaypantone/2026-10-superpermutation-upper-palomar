module

public import upper.regularization.TenPorts
public import upper.certificate.BlockF0

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Regularization.BlockF0
open CircleTransport Transport
open SuperpermutationUpperBound.Native14.Certificate

/-- The only source block requiring more than one old-row lap. -/
def tracks : List (List (Row Nat)) := fiveTracks Certificate.BlockF0.rows 11

private theorem source_length : ∀r∈Certificate.BlockF0.rows,r.base.length=11 := by
  intro r hr
  have hh := (Certificate.BlockF0.rows_basedOn r hr).2.1.length_eq
  simpa using hh

private theorem source_kind : ∀r∈Certificate.BlockF0.rows,
    r.visible=r.base.length ∨ r.visible=r.base.length-2 :=
  fun r hr => (Certificate.BlockF0.rows_basedOn r hr).2.2.2

theorem tracks_length : tracks.length=2 := rfl

theorem tracks_inventory : tracks.flatten.Perm
    (Transport.packingRows Certificate.BlockF0.rows 11) :=
  fiveTracks_inventory _ _ source_length source_kind Certificate.BlockF0.rows_excess

theorem tracks_closed_regular :
    ∀t∈tracks,ClosedTrail t ∧ (11:Int) ∣ signedExcess t :=
  fiveTracks_closed_regular Certificate.BlockF0.rows_closed 11 source_length source_kind
    Certificate.BlockF0.rows_excess


theorem tracks_basedOn : ∀t∈tracks,BasedOn (List.range 12) 12 t := by
  have hb := Certificate.BlockF0.rows_basedOn.transport
    (z:=11) (by decide) (by decide)
  have hp : (11::List.range 11).Perm (List.range 12) := by decide
  intro t ht r hr
  have hm : r ∈ tracks.flatten := List.mem_flatten.mpr ⟨t,ht,hr⟩
  have hh := hb r (tracks_inventory.mem_iff.mp hm)
  exact ⟨hh.1,hh.2.1.trans hp,hh.2.2⟩

/-- Repetition in the definition does not duplicate output row occurrences:
any independently established distinctness of the transport inventory passes
unchanged to these two concatenated tracks. -/
theorem tracks_nodup (h : (Transport.packingRows Certificate.BlockF0.rows 11).Nodup) :
    tracks.flatten.Nodup := tracks_inventory.nodup_iff.mpr h

end SuperpermutationUpperBound.Native14.Regularization.BlockF0
