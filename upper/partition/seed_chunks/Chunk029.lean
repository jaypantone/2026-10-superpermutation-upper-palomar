module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk029
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [2773, 2774, 2775, 2563, 2770, 1203, 3628, 3627, 2777, 2776, 2966, 2965, 2505, 2506, 2507, 2778, 2502, 2503, 2504, 3340, 1371, 4880, 2779, 2501, 2500, 2961, 3988, 3426, 1449, 3669, 1445, 3680]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3712).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 3712).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [2730, 21, 2301, 3892, 3670, 3888, 2015, 1291, 20, 2300, 3672, 3671, 3887, 768, 4894, 19, 2299, 3673, 3674, 3675, 3676, 2964, 4727, 4726, 3667, 2781, 3678, 3677, 2963, 3339, 1370, 3668]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3744).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 3744).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [2780, 3679, 2499, 2962, 975, 1490, 4764, 4763, 866, 472, 471, 266, 4231, 4447, 262, 263, 264, 265, 3241, 561, 2542, 3237, 3238, 3239, 3240, 2619, 560, 2541, 2540, 3400, 3399, 2620]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3776).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 3776).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [3827, 3828, 3829, 3830, 3831, 3398, 3826, 4088, 4087, 4086, 4085, 4860, 602, 1819, 3500, 3933, 2250, 4762, 3387, 2443, 2442, 1521, 3968, 4670, 4761, 1416, 1886, 1885, 164, 3131, 1113, 160]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3808).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 3808).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk029
