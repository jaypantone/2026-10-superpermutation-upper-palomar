module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk009
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [3305, 3306, 3307, 3586, 3585, 3743, 3596, 5012, 2097, 2846, 4021, 3902, 4017, 3260, 1937, 1463, 3906, 54, 2219, 50, 181, 4300, 624, 2223, 70, 544, 4802, 2478, 2477, 2476, 1053, 3957]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1152).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 1152).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [3951, 3952, 3953, 3954, 3955, 3956, 2914, 3950, 3949, 3303, 3302, 1136, 2915, 3297, 3298, 3299, 3300, 3301, 1621, 4076, 3805, 3804, 3803, 5019, 1936, 1866, 3007, 2128, 2127, 2126, 5025, 4299]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1184).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 1184).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [623, 1654, 4464, 2523, 4808, 1057, 1056, 1055, 1054, 2272, 2266, 2267, 2268, 2269, 2270, 2271, 1783, 2265, 2264, 218, 217, 3190, 1784, 212, 213, 214, 215, 216, 3189, 418, 3183, 3184]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1216).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 1216).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [3185, 3186, 3187, 3188, 2387, 4542, 4541, 4540, 5024, 5023, 2606, 4113, 66, 147, 62, 143, 386, 3024, 1669, 65, 64, 63, 142, 387, 4837, 4843, 377, 378, 379, 380, 381, 1470]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1248).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 1248).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk009
