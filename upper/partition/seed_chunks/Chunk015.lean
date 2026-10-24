module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk015
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [575, 576, 577, 578, 579, 3784, 4828, 1919, 1918, 1917, 1916, 4649, 4699, 2519, 2832, 4240, 3019, 1664, 3058, 4698, 2834, 2833, 4239, 2672, 1237, 5010, 4697, 2835, 2836, 2837, 2838, 2839]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1920).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 1920).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [2840, 4759, 2081, 1685, 3016, 3015, 3014, 3013, 4758, 2830, 4148, 3017, 1662, 1661, 1660, 2335, 2831, 4147, 3018, 1663, 2610, 1659, 72, 2520, 4640, 2480, 3149, 76, 3059, 2042, 4990, 4639]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1952).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 1952).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [3454, 3713, 2044, 2043, 225, 226, 978, 221, 222, 223, 224, 1599, 1598, 2070, 1933, 5018, 5017, 786, 4052, 4051, 2819, 4296, 620, 5016, 4399, 2334, 4641, 2330, 3150, 77, 2609, 4645]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1984).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 1984).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [4466, 2521, 907, 1059, 3064, 4470, 3060, 2789, 4989, 906, 1477, 3920, 2791, 2790, 3196, 3197, 3503, 220, 3193, 3194, 3195, 121, 122, 1524, 3971, 118, 119, 120, 394, 393, 759, 2750]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 2016).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 2016).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk015
