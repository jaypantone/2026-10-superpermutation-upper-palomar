module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk000
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [0, 942, 2896, 4364, 3862, 2761, 705, 4704, 2891, 2890, 2889, 3863, 2760, 704, 4418, 2892, 4573, 2888, 3864, 2759, 1316, 4417, 2893, 4572, 4571, 3865, 4844, 4850, 4416, 2894, 1998, 725]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 0).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 0).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [1153, 1612, 4067, 1349, 2895, 4365, 2714, 2934, 1911, 407, 1968, 2215, 931, 3265, 3861, 2762, 706, 331, 4, 4886, 3266, 3860, 4521, 332, 3583, 1311, 3594, 2887, 3771, 2758, 1315, 1458]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 32).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 32).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [4015, 3262, 4900, 1461, 1460, 1459, 3809, 4014, 3263, 726, 1152, 1613, 4068, 2132, 47, 3264, 2715, 2933, 1910, 408, 1967, 938, 937, 936, 4781, 2763, 707, 714, 715, 716, 717, 2564]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 64).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 64).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [2769, 713, 1963, 1962, 719, 718, 1619, 1618, 4073, 1083, 1084, 720, 1079, 1080, 1081, 1082, 3808, 4879, 721, 1078, 1077, 1614, 4069, 2131, 4885, 2710, 3085, 3084, 1725, 409, 992, 2211]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 96).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 96).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk000
