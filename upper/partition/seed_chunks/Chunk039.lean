module

public import upper.partition.BlockWitness

@[expose] public section

/-! Generated finite witnesses. Each assertion checks at most 32 rows;
no generated index or ordinary exporter computation is trusted. -/
namespace SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk039
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def indices00 : List Nat := [1575, 1362, 666, 3044, 4579, 2427, 3252, 3107, 1748, 244, 1592, 4174, 2727, 173, 3140, 4213, 3219, 4045, 508, 1288, 4748, 4747, 240, 239, 238, 509, 1287, 4500, 311, 241, 514, 237]

theorem checked00 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 4992).take 32) indices00 = true := by decide

theorem refines00 : BlockRefines ((canonicalSeedRows.drop 4992).take 32)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked00

def indices01 : List Nat := [510, 1286, 3560, 1577, 242, 513, 512, 511, 5034, 3559, 1576, 243, 1593, 3739, 3600, 2426]

theorem checked01 : blockWitnessCheck completeSeedRows
    ((canonicalSeedRows.drop 5024).take 16) indices01 = true := by decide

theorem refines01 : BlockRefines ((canonicalSeedRows.drop 5024).take 16)
    completeSeedRows :=
  blockWitnessCheck_slice_sound
    (fun r hr => (canonicalSeedRows_basedOn r hr).1)
    (fun r hr => (completeSeedRows_basedOn r hr).1) checked01

end SuperpermutationUpperBound.Native14.Partition.SeedChunks.Chunk039
