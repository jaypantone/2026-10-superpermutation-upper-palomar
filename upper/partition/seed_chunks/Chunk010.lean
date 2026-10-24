module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk010
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [3913, 4711, 3290, 1161, 383, 382, 1469, 3912, 4413, 4028, 1160, 384, 1156, 1468, 3911, 1346, 61, 2941, 385, 2937, 1914, 2228, 67, 146, 145, 144, 4809, 3023, 1668, 1675, 1676, 1677]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1280).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 1280).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [1678, 3855, 3029, 1674, 376, 375, 1680, 1679, 2094, 2093, 2842, 1945, 1946, 1681, 1941, 1942, 1943, 1944, 4023, 4991, 1682, 1940, 1939, 1869, 3010, 56, 4997, 4145, 4303, 4302, 626, 1657]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1312).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 1312).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [68, 546, 3797, 2657, 2570, 3022, 1667, 1000, 999, 4998, 2658, 2569, 2312, 1001, 3293, 1957, 2490, 2659, 2972, 2670, 1235, 1754, 3800, 2654, 5026, 2421, 3114, 1755, 4024, 3799, 2655, 1687]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1344).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 1344).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [850, 1868, 3009, 57, 3798, 2656, 4150, 3369, 1400, 1656, 69, 545, 3218, 4046, 2483, 3717, 2048, 4746, 3213, 3212, 3211, 2484, 3716, 2047, 3292, 3214, 2489, 3210, 2485, 3715, 2046, 4026]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1376).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 1376).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk010
