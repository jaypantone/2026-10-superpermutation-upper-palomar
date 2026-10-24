module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk020
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [4272, 2378, 4331, 2216, 930, 184, 2180, 4600, 2693, 3310, 2284, 4892, 185, 2179, 4599, 3311, 3584, 3744, 3595, 365, 2098, 2847, 3748, 3903, 4016, 3261, 4906, 1462, 3905, 3904, 2220, 49]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2560).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 2560).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [182, 4905, 4904, 2222, 2221, 4548, 48, 183, 1278, 3705, 4271, 2379, 4330, 3461, 3460, 3459, 4787, 4786, 2694, 2701, 2702, 2703, 2704, 1137, 2916, 2700, 4326, 4325, 2706, 2705, 1620, 4075]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2592).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 2592).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [4074, 3092, 3093, 2707, 3088, 3089, 3090, 3091, 1731, 1732, 2708, 3087, 1728, 1729, 1730, 4547, 4884, 2709, 3086, 1727, 1726, 2380, 654, 1484, 1483, 1482, 3925, 4785, 1259, 1266, 1267, 1268]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2624).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 2624).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [1269, 3696, 1785, 1265, 650, 649, 1271, 1270, 3697, 417, 416, 2635, 2634, 1272, 3699, 3698, 2386, 2385, 4198, 4199, 1273, 3700, 4195, 4196, 4197, 4546, 4883, 1274, 3701, 4194, 4193, 2381]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2656).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 2656).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk020
