module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk031
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [3726, 18, 2298, 2297, 3733, 3732, 3825, 3824, 4589, 4590, 4591, 3734, 4586, 4587, 4588, 4092, 432, 4936, 3735, 4585, 4584, 3165, 976, 358, 3155, 82, 867, 229, 470, 2072, 4820, 4441]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3968).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 3968).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [256, 788, 2074, 2073, 2821, 4819, 4818, 3231, 4401, 2823, 2822, 3404, 3405, 3406, 3407, 3401, 3402, 3403, 4099, 4098, 438, 2039, 598, 4867, 3451, 2108, 3156, 83, 792, 230, 603, 3160]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4000).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 4000).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [3501, 4437, 252, 4476, 3388, 3200, 2441, 1522, 3969, 3227, 289, 1417, 125, 1884, 761, 2752, 4817, 154, 1336, 763, 762, 1431, 1432, 1433, 1434, 1428, 1429, 1430, 4100, 440, 439, 2786]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4032).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 4032).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [2581, 4866, 3450, 2859, 797, 4477, 793, 3201, 2586, 3161, 3992, 4438, 253, 4790, 4255, 3689, 3688, 25, 2305, 3228, 4789, 585, 2024, 2023, 1200, 3625, 1437, 674, 675, 676, 677, 530]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4064).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 4064).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk031
