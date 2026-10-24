module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk019
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [1896, 1182, 1181, 455, 274, 1099, 813, 4426, 4345, 4258, 465, 3995, 3994, 5002, 5001, 4346, 4257, 3996, 28, 27, 2307, 5000, 4347, 587, 29, 107, 1198, 3623, 4183, 4348, 1832, 680]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2432).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 2432).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [1103, 815, 3330, 4343, 5028, 449, 1104, 1029, 814, 3329, 4344, 3045, 4578, 454, 275, 1098, 350, 4427, 3577, 4175, 2726, 4750, 345, 344, 343, 342, 4176, 2725, 4749, 346, 3325, 3324]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2464).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 2464).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [3323, 4177, 2724, 106, 347, 3326, 4182, 3322, 4178, 2723, 1031, 348, 3327, 4181, 4180, 4179, 5035, 1030, 349, 3328, 3578, 3738, 1177, 453, 2280, 3465, 1769, 686, 2181, 4601, 2692, 4710]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2496).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 2496).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [1764, 368, 367, 2182, 4602, 2691, 1353, 1765, 846, 366, 2183, 4603, 3749, 1352, 1766, 845, 844, 2184, 4604, 4849, 1351, 1767, 3364, 3363, 1394, 875, 4848, 1350, 1768, 687, 1277, 3704]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2528).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 2528).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk019
