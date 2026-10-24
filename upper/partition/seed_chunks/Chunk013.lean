module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk013
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [1713, 2722, 2342, 4535, 3075, 1716, 1715, 1714, 5036, 2341, 4536, 2358, 1801, 1307, 1176, 4115, 4701, 944, 1835, 35, 1195, 3620, 3056, 4339, 4338, 4836, 36, 1194, 3619, 4340, 4420, 3048]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1664).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 1664).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [4575, 37, 811, 4424, 3052, 4679, 2396, 4000, 4857, 1609, 4064, 4680, 948, 1837, 33, 4856, 4855, 404, 949, 3785, 1836, 34, 1196, 3621, 4185, 4648, 4334, 4636, 933, 103, 1924, 4285]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1696).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 1696).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [3055, 4724, 41, 40, 39, 1925, 4286, 3054, 3581, 42, 1930, 38, 1926, 4287, 3053, 3812, 43, 1929, 1928, 1927, 4288, 4912, 2135, 44, 4292, 4291, 4290, 4289, 4911, 2134, 45, 104]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1728).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 1728).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [1923, 4284, 4186, 4647, 4335, 4635, 4780, 2623, 3724, 2055, 2054, 987, 981, 982, 983, 984, 985, 986, 863, 980, 979, 1606, 1605, 4060, 864, 1600, 1601, 1602, 1603, 1604, 4059, 785]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1760).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 1760).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk013
