module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk032
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [2509, 1436, 1435, 447, 446, 531, 4101, 441, 442, 443, 444, 445, 3449, 2858, 796, 795, 794, 4964, 4581, 3162, 3991, 4439, 254, 1442, 2078, 4260, 2437, 24, 2304, 3229, 3885, 2827]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4096).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 4096).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [590, 1880, 4734, 4733, 1438, 673, 672, 591, 1879, 4096, 436, 1439, 596, 671, 592, 682, 4095, 435, 1440, 595, 594, 593, 4971, 4094, 434, 1441, 2079, 3043, 4580, 3163, 3990, 4440]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4128).take 32) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 4128).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

def indices02 : List Nat := [255, 789, 233, 4173, 2728, 23, 2303, 3230, 4402, 234, 507, 1289, 3146, 3145, 3144, 4943, 235, 506, 3147, 4097, 437, 2040, 597, 236, 3452, 1285, 3157, 84, 791, 231, 4978, 3159]

theorem checked02 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4160).take 32) indices02 = true := by decide

theorem refines02 : BlockRefines ((canonicalSeedRows.drop 4160).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked02

def indices03 : List Nat := [3158, 4093, 433, 790, 232, 3740, 3599, 3164, 4702, 3467, 2974, 2317, 1006, 1953, 1697, 661, 660, 4835, 2318, 1007, 1952, 662, 1355, 1689, 848, 2319, 1008, 1359, 1693, 3790, 4152, 3367]

theorem checked03 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4192).take 32) indices03 = true := by decide

theorem refines03 : BlockRefines ((canonicalSeedRows.drop 4192).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked03

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk032
