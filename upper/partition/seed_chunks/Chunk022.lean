module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk022
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [4553, 3458, 4495, 306, 2695, 4328, 4555, 4554, 3457, 4496, 307, 4954, 4327, 4556, 4557, 4558, 4559, 4560, 4561, 4745, 1595, 2067, 4492, 4491, 4490, 4489, 4744, 4048, 2816, 4493, 304, 303]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2816).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 2816).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [302, 2982, 4552, 2815, 4494, 305, 3843, 301, 653, 1485, 828, 1481, 3924, 3285, 1260, 652, 830, 829, 1480, 3923, 3286, 4953, 651, 831, 832, 833, 834, 835, 836, 2636, 3350, 3351]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2848).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 2848).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [3352, 3353, 3354, 3355, 4743, 390, 756, 2747, 3283, 3282, 3281, 2983, 827, 755, 2746, 3284, 3844, 3280, 1541, 899, 898, 897, 3420, 4799, 739, 746, 747, 748, 749, 2740, 1949, 745]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2880).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 2880).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [1537, 1536, 751, 750, 2741, 838, 837, 3982, 3981, 752, 2743, 2742, 3357, 3356, 3850, 3851, 753, 2744, 3847, 3848, 3849, 2984, 4939, 754, 2745, 3846, 3845, 3279, 2282, 1489, 4765, 2177]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2912).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 2912).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk022
