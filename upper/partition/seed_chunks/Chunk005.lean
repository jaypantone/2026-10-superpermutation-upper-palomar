module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk005
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [3772, 2757, 1314, 1313, 2194, 2195, 2196, 2190, 2191, 2192, 2193, 1854, 1853, 727, 1151, 4871, 4870, 2237, 2993, 2992, 2716, 2932, 1909, 4869, 4657, 3780, 3268, 3776, 4523, 334, 4276, 3272]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 640).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 640).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [3523, 2882, 4794, 2565, 2768, 712, 711, 1961, 2199, 1226, 1227, 1228, 1229, 1230, 1085, 2198, 2197, 1861, 1860, 3001, 1086, 1855, 1856, 1857, 1858, 1859, 3000, 2236, 2994, 2995, 2996, 2997]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 672).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 672).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [2998, 2999, 4656, 3779, 3778, 3777, 4968, 4967, 3839, 3273, 3522, 2883, 2205, 770, 1142, 2921, 4127, 4738, 2200, 1225, 1224, 1143, 2922, 4126, 1850, 2201, 1148, 1223, 1144, 2923, 3663, 1849]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 704).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 704).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [2202, 1147, 1146, 1145, 2924, 4975, 1848, 2203, 2928, 2927, 2926, 2925, 4974, 1847, 2204, 771, 485, 2458, 3838, 3274, 3521, 2884, 4625, 4381, 1318, 1900, 463, 4737, 4620, 3652, 3651, 1984]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 736).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 736).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk005
