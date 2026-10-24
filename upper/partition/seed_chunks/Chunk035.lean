module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk035
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [3939, 2256, 424, 1552, 4852, 2955, 3940, 2862, 800, 423, 1553, 643, 2495, 3441, 2644, 3429, 1452, 2241, 204, 1165, 4162, 1209, 3634, 3895, 4661, 3175, 1166, 496, 4720, 4719, 1561, 1560]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4480).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 4480).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [1559, 1167, 495, 2360, 1803, 1562, 1172, 1558, 1168, 494, 3343, 1374, 1563, 1171, 1170, 1169, 4908, 3342, 1373, 1564, 205, 1164, 2496, 3440, 2645, 3428, 1451, 4776, 4315, 2733, 2732, 1210]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4512).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 4512).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [3635, 3894, 4775, 637, 1294, 1293, 15, 2295, 10, 11, 12, 13, 14, 2173, 4593, 9, 8, 1814, 1813, 2174, 2365, 1808, 1809, 1810, 1811, 1812, 3767, 3554, 1571, 1570, 1569, 4915]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4544).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 4544).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [2497, 3439, 2646, 3427, 1450, 4218, 4316, 2650, 2731, 1211, 3636, 3893, 4217, 638, 1215, 1292, 489, 2462, 4873, 4216, 2120, 491, 490, 1500, 1501, 1502, 1503, 1815, 1498, 1499, 4504, 315]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4576).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 4576).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk035
