module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk026
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [4945, 3317, 4171, 3257, 177, 176, 3143, 4944, 3318, 505, 178, 1640, 1280, 3707, 4269, 3319, 927, 1284, 188, 2102, 2851, 3314, 4979, 190, 189, 1636, 2101, 2850, 3315, 3741, 3598, 195]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3328).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 3328).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [4703, 3466, 4238, 2673, 1238, 870, 1255, 4709, 4233, 4445, 4444, 259, 871, 1254, 1354, 4234, 847, 4443, 258, 872, 2076, 3789, 4235, 3366, 1397, 3233, 873, 2825, 3788, 4236, 3365, 1396]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3360).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 3360).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [1395, 874, 4847, 3787, 4237, 2674, 1239, 2037, 600, 1821, 4332, 4638, 3455, 3153, 80, 869, 1256, 227, 977, 4891, 3154, 81, 868, 228, 1597, 2071, 1932, 4442, 257, 787, 2075, 4050]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3392).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 3392).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [2820, 4295, 619, 3232, 4400, 2824, 4642, 2329, 3151, 78, 4903, 4644, 4643, 4549, 2328, 3152, 79, 2038, 599, 1822, 656, 905, 1478, 3921, 4474, 3390, 1257, 3198, 3502, 4890, 4889, 4475]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3424).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 3424).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk026
