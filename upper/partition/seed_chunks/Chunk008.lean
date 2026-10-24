module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk008
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [2263, 2953, 3942, 2259, 2260, 211, 210, 645, 1071, 4927, 4926, 419, 3182, 3181, 2630, 3078, 1719, 4925, 2388, 4543, 2529, 4539, 3644, 1977, 4190, 4112, 2278, 541, 540, 1772, 4767, 2473]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1024).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 1024).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [1050, 537, 538, 539, 1773, 534, 535, 536, 2274, 2273, 1775, 1774, 1472, 1471, 3914, 1781, 1782, 1776, 1777, 1778, 1779, 1780, 4414, 4823, 1159, 1158, 1157, 1467, 3910, 1347, 4829, 2940]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1056).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 1056).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [2939, 2938, 1915, 2227, 2277, 542, 2085, 1771, 1876, 2474, 1051, 2276, 2087, 2086, 1770, 685, 5005, 5011, 2275, 2088, 2089, 2090, 2091, 2092, 2841, 4753, 2082, 1684, 1873, 1872, 1871, 3012]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1088).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 1088).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [4022, 2083, 1683, 1874, 1938, 1870, 3011, 55, 2084, 4146, 1875, 4301, 625, 1658, 71, 543, 2218, 2479, 180, 2475, 1052, 3709, 4984, 2217, 929, 3712, 3711, 3710, 3308, 3309, 2285, 3304]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1120).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 1120).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk008
