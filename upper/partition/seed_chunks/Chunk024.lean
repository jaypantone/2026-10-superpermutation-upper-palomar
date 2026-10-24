module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk024
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [1261, 2639, 3347, 3346, 1377, 2242, 203, 4952, 2638, 3348, 1379, 1378, 4662, 3174, 4951, 2637, 3349, 1380, 1381, 1382, 1383, 1384, 4742, 2359, 1802, 1306, 200, 199, 198, 1634, 3344, 1375]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3072).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 3072).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [1305, 201, 2165, 197, 1542, 3424, 3423, 3422, 3421, 4798, 738, 2735, 2736, 2737, 2738, 2739, 4314, 2734, 1296, 1297, 1298, 1299, 1300, 636, 1295, 17, 16, 2296, 1302, 1301, 1386, 1385]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3104).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 3104).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [2171, 2172, 4592, 1303, 2168, 2169, 2170, 1635, 4938, 4937, 1304, 2167, 2166, 196, 2283, 359, 186, 2178, 4598, 3312, 4132, 3745, 4821, 364, 2099, 2848, 3747, 3746, 4612, 4613, 4614, 2189]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3136).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 3136).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [4609, 4610, 4611, 883, 884, 885, 3408, 880, 881, 882, 1642, 1641, 1279, 3706, 4270, 4868, 926, 2107, 187, 2103, 2852, 3313, 4275, 191, 3524, 360, 4793, 1138, 2917, 2699, 2698, 4324]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3168).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 3168).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk024
