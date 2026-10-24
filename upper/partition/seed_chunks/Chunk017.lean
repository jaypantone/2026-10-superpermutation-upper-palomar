module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk017
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [4121, 2336, 773, 483, 2456, 4124, 2611, 4120, 3495, 1095, 4385, 1322, 1120, 461, 1702, 3494, 4387, 4386, 1323, 1119, 1995, 5008, 3493, 4388, 1325, 1324, 2898, 4362, 5007, 3492, 4389, 1326]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2176).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 2176).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [1327, 1328, 1329, 1330, 4756, 4383, 1320, 1898, 459, 458, 457, 1027, 4384, 1321, 1897, 460, 1180, 456, 277, 1096, 3432, 1455, 1707, 281, 1703, 729, 4988, 3431, 1454, 2239, 731, 730]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2208).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 2208).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [2718, 4987, 4986, 3897, 4659, 2720, 2719, 4517, 4518, 329, 6, 4514, 4515, 4516, 2363, 2362, 1805, 1309, 1174, 5014, 3769, 1026, 3433, 1456, 1567, 282, 1179, 3437, 276, 1097, 4806, 4805]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2240).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 2240).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [1706, 1705, 1704, 965, 959, 960, 961, 962, 963, 964, 3488, 958, 3483, 3484, 3485, 3486, 3487, 2561, 957, 3482, 3481, 4513, 4512, 2562, 4506, 4507, 4508, 4509, 4510, 4511, 2967, 3336]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2272).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 2272).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk017
