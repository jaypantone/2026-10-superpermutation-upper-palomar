module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk030
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [161, 162, 163, 1188, 3613, 1112, 1111, 1427, 1426, 1189, 2150, 2151, 2152, 2153, 2154, 1425, 2149, 4089, 429, 428, 427, 4859, 2585, 2958, 3993, 3932, 2249, 4676, 4256, 3997, 3687, 26]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3840).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 3840).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [2306, 4669, 4675, 586, 30, 2022, 1199, 3624, 4929, 4674, 1833, 679, 678, 1107, 1108, 1109, 1110, 448, 1105, 1106, 808, 807, 806, 3046, 4577, 4957, 809, 4090, 430, 4677, 426, 3998]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3872).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 3872).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [4582, 2957, 2641, 3931, 2248, 3815, 2244, 3171, 3686, 1206, 3631, 4668, 3816, 4664, 3172, 2021, 1205, 3630, 3818, 3817, 4663, 3173, 4950, 1204, 3629, 3819, 3820, 3821, 3822, 3823, 4741, 4740]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3904).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 3904).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [3579, 3737, 3169, 3168, 3167, 4091, 431, 3814, 3736, 3170, 4583, 3166, 3989, 3425, 1448, 1447, 1446, 4797, 2729, 22, 2302, 3891, 3890, 3889, 4796, 1290, 3727, 3728, 3729, 3730, 3731, 2621]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3936).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 3936).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk030
