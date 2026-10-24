module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk001
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [2003, 2207, 2014, 3720, 2051, 991, 2005, 2004, 2206, 769, 4893, 4899, 990, 2006, 2007, 2008, 2009, 1617, 4072, 4725, 2000, 723, 2011, 2010, 1616, 4071, 3807, 2001, 722, 2012, 1076, 1615]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 128).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 128).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [4070, 2130, 2002, 2711, 2013, 3083, 1724, 410, 3517, 4631, 4368, 4627, 4379, 703, 2798, 3516, 4370, 4369, 4626, 4380, 1317, 4898, 3515, 4371, 4372, 4373, 4374, 698, 414, 4731, 1999, 724]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 160).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 160).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [4376, 4375, 699, 413, 4730, 4366, 2713, 4377, 701, 700, 412, 4544, 4367, 2712, 4378, 702, 4191, 411, 1, 941, 4760, 3857, 3027, 3026, 1671, 3130, 3124, 3125, 3126, 3127, 3128, 3129]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 192).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 192).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [3614, 3123, 3122, 3868, 3867, 1190, 3615, 4567, 4568, 4569, 4570, 3866, 2148, 4566, 2400, 2399, 2398, 4858, 1154, 1611, 4066, 1841, 1840, 1839, 4864, 2935, 1912, 406, 997, 940, 946, 2567]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 224).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 224).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk001
