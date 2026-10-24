module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk016
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [2603, 5015, 1334, 1025, 908, 1021, 3548, 4471, 2608, 912, 4465, 2522, 4807, 1058, 3063, 3062, 3061, 4694, 4688, 4689, 4690, 4691, 4692, 4693, 4252, 4687, 4686, 219, 3192, 3191, 4253, 582]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2048).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 2048).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [956, 955, 3480, 117, 116, 583, 110, 111, 112, 113, 114, 115, 1830, 819, 818, 817, 3332, 5022, 2607, 451, 971, 1093, 1092, 569, 2550, 4771, 1700, 1089, 1090, 1091, 570, 2551]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2080).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 2080).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [1087, 1088, 967, 966, 572, 571, 2552, 2235, 2234, 3490, 3489, 573, 2554, 2553, 4655, 4654, 2559, 2560, 574, 2555, 2556, 2557, 2558, 3783, 4827, 1920, 4281, 4280, 4279, 4650, 970, 1094]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2112).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 2112).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [774, 568, 2549, 4125, 1701, 969, 776, 775, 567, 2548, 3664, 5009, 968, 777, 778, 779, 780, 781, 782, 3491, 4390, 4391, 4392, 4393, 4394, 4395, 4757, 772, 484, 2457, 4123, 4122]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2144).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 2144).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk016
