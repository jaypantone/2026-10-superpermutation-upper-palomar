module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk014
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [4053, 4054, 4055, 4056, 4057, 4058, 4398, 2333, 2332, 2331, 4919, 4918, 4187, 4646, 4336, 4634, 4779, 1192, 3617, 2802, 2801, 3512, 3506, 3507, 3508, 3509, 3510, 3511, 3384, 3505, 3504, 1607]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1792).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 1792).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [4062, 4061, 3385, 1413, 1526, 1525, 3972, 402, 401, 1414, 395, 396, 397, 398, 399, 400, 1333, 1024, 1023, 1022, 3549, 4917, 4188, 913, 4337, 4633, 1101, 1193, 3618, 4341, 2800, 3049]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1824).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 1824).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [4877, 1100, 812, 4425, 3051, 3050, 4683, 4684, 4685, 1608, 4063, 4681, 4682, 952, 953, 954, 3479, 403, 950, 951, 109, 108, 1197, 3622, 4184, 4924, 1831, 820, 1102, 816, 3331, 4342]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1856).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 1856).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [4189, 450, 4700, 2518, 2517, 4241, 4773, 4772, 3057, 2514, 2515, 2516, 4242, 533, 2512, 2513, 4696, 4695, 4244, 4243, 1473, 3916, 3915, 4250, 4251, 4245, 4246, 4247, 4248, 4249, 580, 581]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1888).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 1888).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk014
