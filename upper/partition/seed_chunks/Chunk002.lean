module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk002
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [31, 2765, 709, 1959, 4928, 945, 1834, 2668, 2667, 1232, 3119, 3120, 3121, 2419, 3116, 3117, 3118, 4422, 4421, 3047, 4576, 4956, 810, 4423, 2401, 4678, 2397, 3999, 853, 1610, 4065, 1842]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 256).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 256).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [947, 1838, 32, 3372, 1403, 405, 1966, 939, 2137, 935, 101, 2764, 708, 1965, 2139, 2138, 934, 102, 4949, 4955, 1964, 2140, 2141, 2142, 2143, 2144, 4562, 4739, 3580, 2066, 98, 97]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 288).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 288).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [96, 4488, 2402, 3813, 2065, 99, 854, 95, 4487, 1843, 2136, 2814, 100, 3373, 1404, 300, 993, 2210, 2209, 2208, 4795, 3719, 2050, 2057, 2058, 2059, 2060, 2622, 3725, 2056, 989, 988]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 320).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 320).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [2062, 2061, 2146, 2145, 4563, 861, 862, 2063, 857, 858, 859, 860, 2403, 4935, 2064, 856, 855, 94, 4486, 1844, 4941, 2813, 3375, 3374, 1405, 299, 3518, 4630, 4629, 4628, 4801, 4800]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 352).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 352).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk002
