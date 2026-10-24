module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk038
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [921, 2109, 3561, 1578, 608, 1589, 604, 920, 3249, 4436, 251, 4030, 247, 4041, 2440, 170, 3137, 3226, 4031, 3222, 4042, 1883, 169, 3136, 4033, 4032, 3221, 4043, 4838, 168, 3135, 4034]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4864).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 4864).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [4035, 4036, 4037, 3445, 4713, 4712, 3289, 2592, 4039, 4038, 3444, 2860, 798, 4029, 2591, 4040, 2587, 3443, 3250, 4435, 250, 249, 248, 4811, 2439, 171, 3138, 3225, 3224, 3223, 4810, 1882]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4896).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 4896).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [3031, 3032, 3033, 3034, 3035, 3854, 3030, 167, 3134, 3133, 3037, 3036, 3765, 3764, 3609, 3610, 3611, 3038, 3606, 3607, 3608, 3557, 1574, 4992, 3039, 3605, 3604, 2428, 3251, 3108, 1749, 1361]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4928).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 4928).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [667, 4259, 2438, 172, 3139, 4214, 3796, 668, 589, 1881, 2310, 2309, 2308, 4999, 669, 588, 2311, 4501, 312, 1956, 515, 670, 2971, 681, 3112, 1753, 1363, 665, 5027, 2422, 3113, 3558]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4960).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 4960).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk038
