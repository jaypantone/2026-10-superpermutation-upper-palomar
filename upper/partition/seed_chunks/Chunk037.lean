module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk037
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [2432, 2431, 2430, 3556, 1573, 3754, 3040, 2433, 3603, 2429, 3254, 3105, 1746, 3900, 4170, 3258, 4166, 175, 3142, 4211, 3899, 504, 179, 500, 1281, 3708, 4985, 3898, 928, 1283, 1282, 326]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4736).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 4736).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [327, 328, 7, 323, 324, 325, 2364, 1807, 1806, 3742, 3597, 5013, 3768, 3555, 1572, 3901, 1568, 3259, 3602, 3438, 3253, 3106, 1747, 4804, 4169, 4168, 4167, 174, 3141, 4212, 4803, 503]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4768).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 4768).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [502, 501, 1511, 3958, 1506, 1507, 1508, 1509, 1510, 1134, 2913, 1505, 1504, 322, 321, 1135, 4505, 316, 317, 318, 319, 320, 2968, 3337, 1368, 1367, 1366, 5020, 3601, 2425, 3248, 357]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4800).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 4800).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [3562, 1579, 246, 1590, 469, 3247, 3564, 3563, 1580, 245, 1591, 4840, 3246, 3565, 1582, 1581, 3220, 4044, 4839, 3245, 3566, 1583, 1584, 1585, 1586, 922, 4714, 4499, 310, 609, 1588, 1587]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4832).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 4832).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk037
