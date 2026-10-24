module

public import upper.partition.Extension
public import upper.partition.CanonicalSeed
public import upper.certificate.Halfar0
public import upper.certificate.Halfar1
public import upper.certificate.BlockF0
public import upper.certificate.BlockF1
public import upper.certificate.BlockF2
public import upper.certificate.EmptyLoops

@[expose] public section

/-! The actual native n14 row inventory, kept as symbolic small-data transport
and block replacement rather than a forty-million-row literal certificate. -/
namespace SuperpermutationUpperBound.Native14.Partition
open SuperpermutationUpperBound.Partition
open Certificate

def seedRows : List (Row Nat) := Halfar0.rows ++ Halfar1.rows

def blockRows : List (Row Nat) := BlockF0.rows ++ BlockF1.rows ++ BlockF2.rows

def localRows : List (Row Nat) :=
  Transport.packingRows blockRows 11 ++
    EmptyLoops.blockFEmpty.flatMap (fun x => fullChart x 11 12)

def nativeRows : List (Row Nat) :=
  extendRange seedRows 8 4 ++
    EmptyLoops.halfarAncestors.flatMap
      (fun x => localRows.map (Row.map (relabelSeven x)))

/-- Full rows used solely for the intermediate cyclic-block accounting. -/
def fullAccounting (xs : List (List Nat)) : List (Row Nat) :=
  xs.map (fun x => Row.mk x 12 x.length)

def completeSeedRows : List (Row Nat) :=
  seedRows ++ EmptyLoops.halfarAncestors.flatMap (fun x => fullChart x 7 12)

def completeBlockRows : List (Row Nat) := blockRows ++ fullAccounting EmptyLoops.blockFEmpty

/-- The 5040 extensions of one ordinary seven-cycle by letters 7,8,9,10. -/
def templateBlockRows : List (Row Nat) :=
  extendRange (fullChart (List.range 7) 7 12) 8 3


end SuperpermutationUpperBound.Native14.Partition
