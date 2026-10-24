module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk011
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [3215, 2488, 2487, 2486, 5033, 5039, 4025, 3216, 1594, 2068, 1935, 1867, 3008, 58, 3217, 4047, 2817, 4298, 622, 1655, 4463, 2524, 141, 388, 1062, 3067, 2795, 4752, 136, 135, 134, 1063]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1408).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 1408).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [3068, 2794, 3291, 137, 1068, 133, 1064, 3069, 2793, 4027, 138, 1067, 1066, 1065, 3070, 5038, 60, 139, 3074, 3073, 3072, 3071, 5037, 59, 140, 389, 757, 2748, 2605, 4114, 4458, 2880]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1440).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 1440).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [2344, 2876, 2355, 1046, 4130, 4457, 2346, 2345, 2875, 2356, 1799, 4842, 4456, 2347, 2348, 2349, 2350, 1041, 2232, 4717, 207, 1162, 2352, 2351, 1042, 2231, 4716, 3178, 2943, 2353, 1044, 1043]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1472).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 1472).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [2230, 3781, 2343, 2942, 2354, 1045, 4277, 2229, 4459, 2879, 2878, 2877, 4815, 4814, 4129, 4136, 4137, 4138, 4139, 2176, 4596, 4135, 4455, 4454, 4141, 4140, 2095, 2844, 2843, 4310, 4311, 4142]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1504).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 1504).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk011
