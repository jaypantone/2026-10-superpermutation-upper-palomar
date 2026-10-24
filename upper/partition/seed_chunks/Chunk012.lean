module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk012
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [4306, 4307, 4308, 4309, 632, 633, 4143, 4305, 629, 630, 631, 2338, 4996, 4144, 4304, 628, 627, 4118, 4460, 547, 2122, 1220, 1141, 2920, 4128, 3527, 3526, 5004, 1221, 1140, 2919, 3528]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1536).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 1536).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [3294, 4322, 2491, 1222, 1623, 4078, 3662, 4221, 3801, 2653, 5032, 1864, 3005, 4222, 551, 2124, 1218, 5031, 5030, 1652, 552, 2339, 2123, 1219, 486, 2459, 3837, 4117, 4461, 2526, 2873, 3647]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1568).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 1568).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [1980, 1789, 464, 1548, 1547, 5003, 3648, 1981, 1788, 1549, 209, 646, 1070, 3649, 1982, 420, 1993, 3180, 2631, 3077, 1718, 4349, 2389, 4360, 2530, 4538, 3645, 1978, 5029, 4111, 2531, 2340]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1600).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 1600).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [4537, 3646, 1979, 1790, 2160, 4116, 4462, 2525, 2874, 2357, 1800, 1710, 735, 4751, 4532, 4531, 4530, 341, 1711, 734, 208, 4533, 1069, 4529, 340, 1712, 733, 3179, 4534, 3076, 1717, 3321]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 1632).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 1632).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk012
