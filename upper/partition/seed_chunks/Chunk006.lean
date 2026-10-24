module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk006
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [1901, 462, 1851, 4621, 1149, 3650, 1983, 1902, 1994, 2990, 4622, 2930, 1907, 4350, 1903, 4361, 2989, 4623, 2929, 1906, 1905, 1904, 4973, 2988, 4624, 4382, 1319, 1899, 2161, 3275, 3520, 2885]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 768).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 768).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [3773, 4526, 337, 1709, 736, 279, 278, 4947, 4527, 338, 1708, 280, 1852, 728, 1150, 4528, 339, 2238, 732, 2991, 2717, 2931, 1908, 3320, 4658, 2721, 3269, 3775, 4524, 335, 4980, 3271]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 800).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 800).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [3270, 2987, 3774, 4525, 336, 1308, 1175, 3276, 2279, 943, 2392, 4004, 2628, 2472, 1049, 1974, 1973, 4830, 4005, 2627, 3642, 1975, 4419, 1793, 4574, 4006, 2871, 2468, 1797, 2257, 2395, 4001]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 832).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 832).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [4851, 2954, 3941, 2258, 4415, 2394, 4002, 644, 1072, 1466, 3909, 1348, 2393, 4003, 2629, 3079, 1720, 2226, 1969, 2214, 932, 3176, 2945, 2471, 1048, 4718, 4010, 4009, 4008, 2946, 2470, 1047]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 864).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 864).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk006
