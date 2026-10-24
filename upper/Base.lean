module

public import upper.Family
public import upper.partition.Coverage
public import upper.partition.Counts
public import upper.pointers.Cover

@[expose] public section

namespace SuperpermutationUpperBound.Native14

/-- The saved fourteen-letter base construction, with every finite premise
discharged by structural proofs and kernel-checked small certificates. -/
noncomputable def nativeBase : Family.Base SeedFamily.Index where
  baseRows := Partition.nativeRows
  baseLabels := SeedFamily.labels
  baseFamily := SeedFamily.family
  baseCircles := Pointers.circles
  labels_complete := SeedFamily.labels_complete
  labels_nodup := SeedFamily.labels_nodup
  inventory := SeedFamily.family_inventory
  basedOn := Partition.nativeRows_basedOn
  complete := Partition.nativeRows_complete
  row_count := Partition.nativeRows_length
  charge := Partition.nativeRows_charge
  closed := SeedFamily.family_closed
  winding := SeedFamily.family_winding
  circles_valid := Pointers.circles_valid
  circles_support := Pointers.circles_support
  circle_count := Pointers.circles_length
  safe_cover := Pointers.safe_cover

end SuperpermutationUpperBound.Native14
