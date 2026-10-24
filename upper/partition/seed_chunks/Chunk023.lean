module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk023
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [4597, 4134, 4133, 4453, 4230, 4448, 4449, 4450, 4451, 4452, 4312, 4229, 4228, 2188, 4608, 4607, 4313, 634, 559, 558, 2539, 879, 878, 635, 1388, 1389, 1390, 1391, 1392, 877, 1387, 1631]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2944).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 2944).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [1630, 1629, 4084, 4861, 4274, 1818, 3525, 1488, 1494, 1139, 2918, 3529, 2697, 4323, 4933, 1493, 1624, 4079, 3661, 3660, 4225, 4226, 4227, 1863, 3004, 4223, 4224, 555, 556, 557, 2538, 1651]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2976).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 2976).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [553, 554, 2117, 2116, 487, 2460, 3836, 4959, 2118, 1632, 1495, 1628, 4083, 3530, 3841, 1817, 1546, 1487, 3937, 2254, 1787, 1550, 1262, 647, 4932, 3936, 2253, 421, 1992, 1991, 2632, 4931]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3008).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 3008).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [4930, 4673, 2390, 4359, 4358, 2534, 2535, 2536, 2537, 4110, 2532, 2533, 2868, 2867, 805, 1791, 2159, 4958, 2869, 1633, 3938, 2255, 425, 1551, 2164, 2956, 2640, 1486, 3345, 1376, 2243, 202]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3040).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 3040).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk023
