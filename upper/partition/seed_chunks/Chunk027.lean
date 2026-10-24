module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk027
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [3389, 3199, 123, 1523, 3970, 4888, 288, 1418, 124, 392, 760, 2751, 2602, 155, 1335, 764, 909, 1020, 3547, 4472, 4902, 911, 910, 824, 1019, 3546, 4473, 2785, 2582, 1823, 655, 3929]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3456).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 3456).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [3928, 3927, 3926, 4784, 1258, 3691, 3692, 3693, 3694, 3695, 4254, 3690, 2026, 2027, 2028, 2029, 2030, 584, 2025, 1202, 1201, 3626, 2032, 2031, 1829, 1828, 528, 529, 2508, 2033, 525, 526]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3488).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 3488).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [527, 823, 4882, 4881, 2034, 524, 523, 1824, 3987, 901, 2677, 1242, 1444, 1253, 741, 3986, 2679, 2678, 1243, 1443, 2077, 4896, 3985, 2680, 1245, 1244, 3886, 2826, 4895, 3984, 2681, 1246]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3520).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 3520).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [1247, 1248, 1249, 1827, 4728, 2675, 1240, 2036, 1251, 1250, 1826, 822, 2676, 1241, 2035, 1252, 522, 1825, 974, 1491, 566, 2547, 3665, 3393, 3682, 4708, 4232, 4446, 261, 260, 3394, 3681]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3552).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 3552).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk027
