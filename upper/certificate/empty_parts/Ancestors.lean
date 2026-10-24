module

public import upper.certificate.Checks

@[expose] public section

/-! Preserved omitted-loop strings. Every permutation check decodes at most32 strings. -/
namespace SuperpermutationUpperBound.Native14.Certificate.EmptyLoopParts.Ancestors
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List String := [
  "0132456",
  "0136524",
  "0142365",
  "0145623",
  "0152634",
  "0154326",
  "0162543",
  "0163425",
  "0231546",
  "0236415",
  "0241635",
  "0245316",
  "0251364",
  "0254613",
  "0261453",
  "0263514",
  "0312564",
  "0316452",
  "0321465",
  "0326541",
  "0345261",
  "0346125",
  "0354162",
  "0356214",
  "0412653",
  "0415362",
  "0421356",
  "0425631",
  "0435126",
  "0436251",
  "0463152",
  "0465213"
]

theorem length00 : encoded00.length = 32 := by rfl

def bases00 : List (List Nat) := encoded00.map (fun x => x.toList.map decodeLetter)

theorem checked00 : bases00.all (fun x => decide (x.Perm (List.range 7))) = true := by rfl

def encoded01 : List String := [
  "0512346",
  "0514632",
  "0521643",
  "0524361",
  "0534216",
  "0536142",
  "0563241",
  "0564123",
  "0612435",
  "0613542",
  "0621534",
  "0623451",
  "0643215",
  "0645132",
  "0653124",
  "0654231"
]

theorem length01 : encoded01.length = 16 := by rfl

def bases01 : List (List Nat) := encoded01.map (fun x => x.toList.map decodeLetter)

theorem checked01 : bases01.all (fun x => decide (x.Perm (List.range 7))) = true := by rfl

def encoded : List String :=
  encoded00 ++
  encoded01

theorem encoded_length : encoded.length = 48 := by
  simp only [encoded, List.length_append, length00, length01, Nat.reduceAdd]

def bases : List (List Nat) := encoded.map (fun x => x.toList.map decodeLetter)

theorem bases_blocks : bases =
  bases00 ++
  bases01 := by
  simp only [bases, encoded, List.map_append, bases00, bases01]

theorem bases_length : bases.length = 48 := by
  rw [bases, List.length_map]
  exact encoded_length

theorem checked : bases.all (fun x => decide (x.Perm (List.range 7))) = true := by
  simp only [bases_blocks, List.all_append, checked00, checked01, Bool.and_self]

end SuperpermutationUpperBound.Native14.Certificate.EmptyLoopParts.Ancestors
