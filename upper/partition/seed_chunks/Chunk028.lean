module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk028
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [4707, 562, 2543, 3236, 3235, 3395, 2016, 2114, 563, 2544, 3834, 3234, 3396, 767, 2113, 564, 2545, 3833, 3832, 3397, 4846, 2112, 565, 2546, 3666, 2782, 601, 1820, 3499, 3934, 2251, 1118]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3584).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 3584).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [1996, 3392, 3683, 1520, 3967, 4671, 2897, 4363, 1421, 2018, 4706, 4705, 1114, 159, 158, 1422, 2017, 2865, 803, 1115, 2157, 157, 1423, 766, 2864, 802, 1116, 2156, 2155, 1424, 4845, 2863]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3616).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 3616).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [801, 1117, 1997, 2783, 2584, 2959, 2643, 3430, 1453, 2240, 285, 3391, 3684, 1208, 3633, 3896, 4660, 286, 1420, 2019, 4519, 330, 5, 4887, 287, 1419, 4520, 2361, 1804, 1310, 1173, 156]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3648).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 3648).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [3770, 765, 3434, 1457, 1566, 283, 4901, 3436, 3435, 3341, 1372, 1565, 284, 2784, 2583, 2960, 2642, 3930, 2247, 2246, 2245, 4783, 3685, 1207, 3632, 4667, 4666, 4665, 4782, 2020, 2771, 2772]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 3680).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 3680).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk028
