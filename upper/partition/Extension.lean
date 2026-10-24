module

public import upper.partition.Relabel

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Partition
open SuperpermutationUpperBound.Partition

def extendRange (rs : List (Row Nat)) (n : Nat) : Nat → List (Row Nat)
  | 0 => rs
  | k+1 => Transport.packingRows (extendRange rs n k) (n+k)

theorem basedOn_perm_alphabet {a b : List Nat} {s : Nat} {rs : List (Row Nat)}
    (h : BasedOn a s rs) (hp : a.Perm b) : BasedOn b s rs := by
  intro r hr
  have hh := h r hr
  exact ⟨hh.1, hh.2.1.trans hp, hh.2.2⟩

theorem blockComplete_perm_alphabet {a b : List Nat} {rs : List (Row Nat)}
    (h : BlockComplete a rs) (hp : a.Perm b) : BlockComplete b rs := by
  intro x hx
  exact h x (hx.trans hp.symm)

theorem basedOn_transport_range {rs : List (Row Nat)} {n s : Nat}
    (h : BasedOn (List.range n) s rs) (hns : n ≠ s) :
    BasedOn (List.range (n+1)) s (Transport.packingRows rs n) := by
  apply basedOn_perm_alphabet (h.transport (by simp) hns)
  rw [List.range_succ]
  simpa using (List.perm_append_comm (l₁ := [n]) (l₂ := List.range n))

theorem extendRange_basedOn {rs : List (Row Nat)} {n s : Nat}
    (h : BasedOn (List.range n) s rs) (k : Nat) (hns : n+k ≤ s) :
    BasedOn (List.range (n+k)) s (extendRange rs n k) := by
  induction k with
  | zero => simpa only [extendRange, Nat.add_zero] using h
  | succ k ih =>
      have hi := ih (by omega)
      simpa only [extendRange, Nat.add_assoc] using basedOn_transport_range hi (by omega)

theorem extendRange_complete {rs : List (Row Nat)} {n s : Nat}
    (hc : BlockComplete (List.range n) rs) (hb : BasedOn (List.range n) s rs)
    (hn : 0 < n) (k : Nat) (hns : n+k ≤ s) :
    BlockComplete (List.range (n+k)) (extendRange rs n k) := by
  induction k with
  | zero => simpa only [extendRange, Nat.add_zero] using hc
  | succ k ih =>
      have hc' := ih (by omega)
      have hb' := extendRange_basedOn hb k (by omega)
      have ht := hc'.transport (z := n+k) hb' List.nodup_range (by simp; omega) (by simp)
      apply blockComplete_perm_alphabet ht
      rw [show n+(k+1)=(n+k)+1 by omega, List.range_succ]
      simpa using (List.perm_append_comm (l₁ := [n+k]) (l₂ := List.range (n+k)))

theorem extendRange_append (rs ts : List (Row Nat)) (n k : Nat) :
    extendRange (rs++ts) n k = extendRange rs n k ++ extendRange ts n k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [extendRange, ih, Transport.packingRows, List.flatMap_append]

theorem extendRange_flatMap {ι : Type} (is : List ι) (f : ι → List (Row Nat)) (n k : Nat) :
    extendRange (is.flatMap f) n k = is.flatMap (fun i => extendRange (f i) n k) := by
  induction is with
  | nil => induction k <;> simp_all [extendRange, Transport.packingRows]
  | cons i is ih => simpa [List.flatMap_cons, extendRange_append] using congrArg (List.append (extendRange (f i) n k)) ih

theorem extendRange_map (rs : List (Row Nat)) (f : Nat → Nat) (n k : Nat)
    (hf : ∀ j < k, f (n+j) = n+j) :
    extendRange (rs.map (Row.map f)) n k = (extendRange rs n k).map (Row.map f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [extendRange, ih (fun j hj => hf j (by omega))]
      rw [← hf k (by omega), transport_packingRows_map]
      rfl

theorem extendRange_refines {rs ts : List (Row Nat)} {n s : Nat}
    (h : BlockRefines rs ts) (hr : BasedOn (List.range n) s rs)
    (ht : BasedOn (List.range n) s ts) (k : Nat) (hns : n+k ≤ s) :
    BlockRefines (extendRange rs n k) (extendRange ts n k) := by
  induction k with
  | zero => exact h
  | succ k ih =>
      apply BlockRefines.transport (ih (by omega))
      · exact fun r hrmem => (extendRange_basedOn hr k (by omega) r hrmem).1
      · exact fun t htmem => (extendRange_basedOn ht k (by omega) t htmem).1

end SuperpermutationUpperBound.Native14.Partition
