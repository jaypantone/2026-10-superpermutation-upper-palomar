module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk003
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [2797, 2804, 2805, 2806, 2807, 1191, 3616, 2803, 3514, 3513, 2809, 2808, 2147, 4565, 4564, 3382, 3383, 2810, 3378, 3379, 3380, 3381, 1411, 1412, 2811, 3377, 1408, 1409, 1410, 2985, 4940, 2812]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 384).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 384).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [3376, 1407, 1406, 3278, 2, 148, 290, 3858, 126, 3025, 1670, 2753, 4816, 153, 1337, 2756, 2755, 2754, 3873, 3874, 3875, 3869, 3870, 3871, 3872, 2411, 2410, 2787, 2580, 4865, 1475, 3918]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 416).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 416).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [4412, 4478, 4408, 3202, 1155, 90, 4482, 1345, 291, 1341, 127, 2936, 1913, 295, 996, 149, 4788, 2566, 2767, 2766, 710, 1960, 3878, 2663, 2664, 2665, 2666, 1231, 2510, 3877, 3876, 2418]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 448).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 448).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [2417, 532, 2511, 2412, 2413, 2414, 2415, 2416, 1474, 3917, 4411, 4410, 4409, 4963, 852, 91, 4483, 1344, 1343, 1342, 4969, 3371, 1402, 296, 995, 150, 3884, 2828, 2571, 3021, 1666, 4732]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 480).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 480).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk003
