module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk033
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [1398, 3537, 3794, 4156, 3471, 2976, 2315, 1004, 4854, 2375, 3472, 3786, 2975, 2316, 1005, 1954, 517, 917, 4333, 4637, 3456, 4497, 308, 611, 1696, 4723, 2323, 2322, 2321, 1010, 612, 1695]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4224).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 4224).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [1596, 2324, 1931, 2320, 1009, 613, 1694, 4049, 2325, 4294, 618, 3538, 614, 4157, 4551, 2326, 4293, 617, 616, 615, 4910, 4550, 2327, 4498, 309, 610, 518, 916, 657, 904, 1479, 3922]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4256).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 4256).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [3287, 2594, 4161, 4722, 1014, 1013, 1012, 1011, 2595, 4160, 4721, 1015, 3542, 3541, 3540, 2596, 4159, 391, 1016, 3543, 2601, 3539, 2597, 4158, 826, 1017, 3544, 2600, 2599, 2598, 4909, 825]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4288).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 4288).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [1018, 3545, 3288, 2593, 519, 915, 658, 903, 4778, 4777, 1950, 744, 743, 1535, 1529, 1530, 1531, 1532, 1533, 1534, 3980, 1528, 3975, 3976, 3977, 3978, 3979, 3852, 1527, 3974, 3973, 2373]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4320).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 4320).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk033
