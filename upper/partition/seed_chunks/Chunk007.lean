module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk007
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [3582, 4011, 3593, 4007, 2947, 2469, 1798, 3811, 4012, 3592, 3591, 2948, 4907, 4913, 3810, 4013, 206, 1163, 1073, 1465, 3908, 2133, 46, 3177, 2944, 3080, 1721, 2225, 1970, 2213, 4774, 2624]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 896).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 896).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [3723, 3722, 2053, 2294, 2288, 2289, 2290, 2291, 2292, 2293, 4594, 2287, 2286, 2951, 2950, 2175, 4595, 3587, 3588, 3589, 3590, 2949, 2096, 2845, 4020, 4019, 4018, 4914, 1074, 1464, 3907, 53]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 928).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 928).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [52, 51, 4920, 3081, 1722, 2224, 1971, 2212, 549, 2625, 1216, 3721, 2052, 2463, 4872, 548, 2121, 2466, 2465, 2464, 3946, 3947, 3948, 2952, 3943, 3944, 3945, 3296, 3295, 4321, 2492, 4921]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 960).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 960).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [1622, 4077, 3806, 4220, 3802, 2652, 1075, 1865, 3006, 2129, 550, 2125, 1217, 3082, 1723, 1653, 1972, 4632, 2528, 2626, 3643, 1976, 2799, 1794, 4878, 2527, 2872, 2467, 1796, 1795, 2261, 2262]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 992).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 992).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk007
