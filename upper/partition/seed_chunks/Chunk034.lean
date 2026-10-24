module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk034
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [2372, 3853, 2366, 2367, 2368, 2369, 2370, 2371, 3766, 3553, 3552, 3551, 3550, 4916, 520, 914, 659, 902, 3110, 1751, 1951, 663, 742, 1690, 4876, 3109, 1750, 1360, 1692, 1691, 4153, 4875]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4352).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 4352).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [4874, 4215, 3795, 4155, 4154, 3475, 3476, 3477, 3478, 2374, 3473, 3474, 4503, 4502, 313, 1955, 516, 4923, 2970, 821, 3111, 1752, 1364, 664, 521, 2423, 973, 1492, 1625, 4080, 3533, 4318]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4384).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 4384).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [1698, 2648, 2647, 4834, 4833, 3534, 4317, 2649, 1213, 1212, 3637, 4832, 3535, 639, 1214, 2115, 488, 2461, 3835, 3536, 2119, 492, 1496, 1627, 4082, 3531, 4853, 1816, 1497, 2111, 1626, 4081]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4416).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 4416).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [3532, 4319, 2494, 918, 3498, 3935, 2252, 422, 1554, 642, 4163, 1519, 3966, 4672, 2391, 1555, 641, 497, 3640, 3639, 3638, 4831, 1556, 640, 3641, 2866, 804, 1792, 2158, 1557, 2870, 493]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4448).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 4448).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk034
