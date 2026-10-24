module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk036
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [314, 4320, 2493, 4922, 2969, 3338, 1369, 4219, 1365, 2651, 2498, 2424, 972, 3102, 3101, 1742, 1123, 4770, 1699, 3098, 3099, 3100, 1741, 1124, 3096, 3097, 1737, 1738, 1739, 1740, 1125, 1735]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4608).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 4608).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [1736, 1513, 1512, 3959, 1127, 1126, 924, 923, 1132, 1133, 2912, 1128, 1129, 1130, 1131, 2110, 4826, 4825, 607, 606, 605, 919, 3497, 3103, 1744, 1743, 1122, 4769, 4164, 1518, 3965, 4209]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4640).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 4640).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [4208, 2901, 4768, 498, 4204, 4205, 4206, 4207, 2902, 4202, 4203, 1514, 3961, 3960, 2904, 2903, 3447, 3446, 2909, 2910, 2911, 2905, 2906, 2907, 2908, 2861, 799, 4824, 2590, 2589, 2588, 3442]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4672).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 4672).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [3496, 3104, 1745, 3755, 1121, 2434, 4165, 1517, 3964, 4210, 3756, 2900, 1877, 499, 1516, 3963, 3758, 3757, 2899, 684, 5006, 1515, 3962, 3759, 3760, 3761, 3762, 3763, 4755, 4754, 3753, 3041]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4704).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 4704).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk036
