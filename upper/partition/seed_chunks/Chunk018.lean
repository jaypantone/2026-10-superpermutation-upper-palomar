module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk018
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [3335, 3334, 3333, 5021, 1178, 452, 271, 356, 1033, 352, 4429, 3575, 468, 270, 1035, 1034, 351, 4428, 3576, 4841, 269, 1036, 1037, 1038, 1039, 1040, 2233, 3244, 3567, 3568, 3569, 3570]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2304).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 2304).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [3571, 4653, 4715, 105, 1922, 4283, 3573, 3572, 4652, 3782, 1032, 1921, 4282, 3574, 4278, 4651, 272, 355, 354, 353, 4430, 4813, 467, 474, 475, 476, 477, 2450, 865, 473, 268, 267]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2336).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 2336).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [479, 478, 2451, 784, 783, 3243, 3242, 480, 2453, 2452, 4397, 4396, 2617, 2618, 481, 2454, 2614, 2615, 2616, 2337, 4995, 482, 2455, 2613, 2612, 4119, 273, 4434, 4433, 4432, 4431, 4812]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2368).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 2368).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [466, 2445, 2446, 2447, 2448, 2449, 3386, 2444, 1888, 1889, 1890, 1891, 1892, 1415, 1887, 166, 165, 3132, 1894, 1893, 1332, 1331, 1186, 1187, 3612, 1895, 1183, 1184, 1185, 1028, 4994, 4993]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2400).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 2400).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk018
