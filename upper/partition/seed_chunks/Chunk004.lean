module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk004
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [3879, 2662, 2661, 2572, 3020, 1665, 2407, 3880, 2577, 2660, 2573, 2671, 1236, 2406, 3881, 2576, 2575, 2574, 4970, 4976, 2405, 3882, 2080, 1686, 851, 92, 4484, 1846, 3883, 2829, 4149, 3370]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 512).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 512).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [1401, 297, 994, 151, 4403, 3207, 2482, 3718, 2049, 74, 73, 4942, 3208, 2481, 3148, 75, 2408, 2041, 2578, 3209, 3453, 3714, 2045, 85, 4406, 3204, 4977, 88, 87, 86, 2404, 4405]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 544).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 544).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [3205, 2069, 1934, 93, 4485, 1845, 4404, 3206, 2818, 4297, 621, 298, 3519, 152, 1338, 130, 1061, 3066, 2796, 4468, 4467, 4948, 131, 1060, 3065, 4469, 2409, 2788, 2579, 132, 1476, 3919]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 576).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 576).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [2792, 4479, 4407, 3203, 4983, 89, 4481, 4480, 292, 1340, 128, 4982, 4981, 294, 293, 2986, 1339, 129, 758, 2749, 2604, 3277, 3, 2881, 3267, 3859, 4522, 333, 4131, 1312, 4822, 2886]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 608).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 608).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk004
