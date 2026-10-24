module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk025
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [4617, 3655, 3656, 3657, 3658, 3659, 3094, 4616, 4615, 1862, 3003, 3002, 3095, 1733, 887, 886, 3409, 1650, 1649, 1734, 1643, 1644, 1645, 1646, 1647, 1648, 925, 2106, 2105, 2104, 2853, 4966]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3200).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 3200).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [3840, 192, 1545, 361, 4792, 4791, 1786, 1264, 1263, 648, 4618, 3654, 1987, 1988, 1989, 1990, 2633, 889, 3412, 4354, 4355, 4356, 4357, 4200, 888, 3411, 3410, 4109, 4108, 4201, 4102, 4103]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3232).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 3232).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [4104, 4105, 4106, 4107, 3448, 2857, 2856, 2855, 2854, 4965, 2163, 193, 1544, 362, 894, 3417, 3751, 4261, 2436, 4736, 4619, 3653, 1986, 1985, 4262, 2435, 4735, 890, 3413, 4353, 4352, 4263]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3264).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 3264).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [1878, 1639, 891, 3414, 4268, 4351, 4264, 683, 1638, 892, 3415, 4267, 4266, 4265, 4972, 1637, 893, 3416, 3752, 3042, 2162, 194, 1543, 363, 2100, 2849, 3316, 4172, 737, 3256, 3255, 4946]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3296).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 3296).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk025
