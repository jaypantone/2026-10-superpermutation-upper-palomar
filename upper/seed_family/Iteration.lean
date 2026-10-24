module

public import upper.seed_family.Lift
public import upper.partition.Extension

@[expose] public section

namespace SuperpermutationUpperBound.Native14.SeedFamily
open CircleTransport Transport

def iterate (h : Nat) (families : List (List (Row Nat))) : Nat → List (List (Row Nat))
  | 0 => families
  | k+1 => step (h+k) (h+k+1) (iterate h families k)

theorem iterate_regular (h : Nat) (hn : 3≤h+1)
    {families : List (List (Row Nat))} (hr : Regular h families) (k : Nat) :
    Regular (h+k) (iterate h families k) := by
  induction k with
  | zero => simpa only [iterate,Nat.add_zero] using hr
  | succ k ih =>
      simpa only [iterate,Nat.add_assoc] using step_regular (h+k) (by omega) (h+k+1) ih

theorem iterate_inventory (h : Nat) (hn : 3≤h+1)
    {families : List (List (Row Nat))} (hr : Regular h families) (k : Nat) :
    (iterate h families k).flatten.Perm (Partition.extendRange families.flatten (h+1) k) := by
  induction k with
  | zero => exact List.Perm.refl _
  | succ k ih =>
      have hs := iterate_regular h hn hr k
      have ht := step_inventory (h+k) (by omega) (h+k+1) (iterate h families k)
        (fun rs hrs r hmem => ((hs rs hrs).2.2 r hmem).1)
      have hh := ht.trans (packingRows_perm ih (h+k+1))
      simpa only [iterate,Partition.extendRange,show h+k+1=h+1+k by omega] using hh

end SuperpermutationUpperBound.Native14.SeedFamily
