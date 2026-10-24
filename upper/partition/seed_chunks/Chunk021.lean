module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk021
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [1540, 900, 690, 896, 3419, 2690, 740, 1539, 692, 691, 895, 3418, 3750, 4897, 1538, 693, 694, 695, 696, 697, 415, 3983, 2682, 2683, 2684, 2685, 2686, 2384, 4729, 688, 1276, 3703]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2688).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 2688).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [2688, 2687, 2383, 4545, 689, 1275, 3702, 2689, 4192, 2382, 2281, 3464, 4766, 3856, 3028, 1673, 1672, 374, 1763, 369, 370, 371, 372, 373, 1947, 1762, 1761, 2187, 2186, 4606, 1948, 840]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2720).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 2720).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [841, 842, 843, 2185, 4605, 839, 3359, 3360, 3361, 3362, 1393, 876, 3358, 2980, 2979, 2978, 4863, 4862, 4273, 2377, 998, 3463, 3469, 2568, 2313, 1002, 2696, 1958, 4934, 3468, 2973, 2669]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2752).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 2752).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [1234, 1233, 1758, 1759, 1760, 2420, 3115, 1756, 1757, 1357, 1356, 1688, 849, 4962, 4961, 1358, 3792, 3791, 4151, 3368, 1399, 4960, 3793, 2981, 3470, 2977, 2314, 1003, 3842, 2376, 4329, 3462]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2784).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 2784).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk021
