module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original BlockF0 rows 512 through 713.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.BlockF0Parts.C01
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("80A12345679", 11),
  ("0A123456789", 11),
  ("A1234567809", 11),
  ("123456780A9", 9),
  ("912345678A0", 9),
  ("091234567A8", 11),
  ("91234567A08", 9),
  ("8912345670A", 11),
  ("9123456708A", 11),
  ("1234567089A", 9),
  ("A1234567098", 11),
  ("123456709A8", 11),
  ("23456709A18", 9),
  ("8234567091A", 11),
  ("2345670918A", 11),
  ("3456709182A", 11),
  ("4567091823A", 11),
  ("5670918234A", 11),
  ("6709182345A", 11),
  ("7091823456A", 11),
  ("0918234567A", 11),
  ("9182345670A", 9),
  ("A9182345607", 11),
  ("918234560A7", 11),
  ("18234560A97", 9),
  ("7182345609A", 11),
  ("1823456097A", 11),
  ("8234560971A", 9),
  ("A8234560917", 9),
  ("7A823456019", 11),
  ("A8234560179", 11),
  ("823456017A9", 11)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 18 := by decide

theorem based00 : basedOnCheck (List.range 11) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("80A12345679", 11)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("23456017A89", 11)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("23456017A89", 11),
  ("3456017A829", 9),
  ("93456017A28", 9),
  ("8934560172A", 11),
  ("9345601728A", 11),
  ("3456017289A", 9),
  ("A3456017298", 11),
  ("345601729A8", 11),
  ("45601729A38", 9),
  ("8456017293A", 11),
  ("4560172938A", 11),
  ("5601729384A", 11),
  ("6017293845A", 11),
  ("0172938456A", 11),
  ("1729384560A", 11),
  ("7293845601A", 11),
  ("2938456017A", 11),
  ("9384560172A", 9),
  ("A9384560127", 11),
  ("938456012A7", 11),
  ("38456012A97", 9),
  ("7384560129A", 11),
  ("3845601297A", 11),
  ("8456012973A", 9),
  ("A8456012937", 9),
  ("7A845601239", 11),
  ("A8456012379", 11),
  ("845601237A9", 11),
  ("45601237A89", 11),
  ("5601237A849", 9),
  ("95601237A48", 9),
  ("8956012374A", 11)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 20 := by decide

theorem based01 : basedOnCheck (List.range 11) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("23456017A89", 11)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("9560123748A", 11)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("9560123748A", 11),
  ("5601237489A", 9),
  ("A5601237498", 11),
  ("560123749A8", 11),
  ("60123749A58", 9),
  ("8601237495A", 11),
  ("6012374958A", 11),
  ("0123749586A", 11),
  ("1237495860A", 11),
  ("2374958601A", 11),
  ("3749586012A", 11),
  ("7495860123A", 11),
  ("4958601237A", 11),
  ("9586012374A", 9),
  ("A9586012347", 11),
  ("958601234A7", 11),
  ("58601234A97", 9),
  ("7586012349A", 11),
  ("5860123497A", 11),
  ("8601234975A", 9),
  ("A8601234957", 9),
  ("7A860123459", 11),
  ("A8601234579", 11),
  ("860123457A9", 11),
  ("60123457A89", 11),
  ("0123457A869", 9),
  ("90123457A68", 9),
  ("8901234576A", 11),
  ("9012345768A", 11),
  ("0123457689A", 9),
  ("A0123457698", 11),
  ("012345769A8", 11)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 18 := by decide

theorem based02 : basedOnCheck (List.range 11) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("9560123748A", 11)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("12345769A08", 9)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("12345769A08", 9),
  ("8123457690A", 11),
  ("1234576908A", 11),
  ("2345769081A", 11),
  ("3457690812A", 11),
  ("4576908123A", 11),
  ("5769081234A", 11),
  ("7690812345A", 11),
  ("6908123457A", 11),
  ("9081234576A", 9),
  ("A9081234567", 11),
  ("908123456A7", 11),
  ("08123456A97", 9),
  ("7081234569A", 11),
  ("0812345697A", 11),
  ("8123456970A", 9),
  ("A8123456907", 9),
  ("7A812345609", 11),
  ("A8123456079", 11),
  ("812345607A9", 11),
  ("12345607A89", 11),
  ("2345607A819", 9),
  ("92345607A18", 9),
  ("8923456071A", 11),
  ("9234560718A", 11),
  ("2345607189A", 9),
  ("A2345607198", 11),
  ("234560719A8", 11),
  ("34560719A28", 9),
  ("8345607192A", 11),
  ("3456071928A", 11),
  ("4560719283A", 11)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 18 := by decide

theorem based03 : basedOnCheck (List.range 11) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("12345769A08", 9)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("5607192834A", 11)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("5607192834A", 11),
  ("6071928345A", 11),
  ("0719283456A", 11),
  ("7192834560A", 11),
  ("1928345607A", 11),
  ("9283456071A", 9),
  ("A9283456017", 11),
  ("928345601A7", 11),
  ("28345601A97", 9),
  ("7283456019A", 11),
  ("2834560197A", 11),
  ("8345601972A", 9),
  ("A8345601927", 9),
  ("7A834560129", 11),
  ("A8345601279", 11),
  ("834560127A9", 11),
  ("34560127A89", 11),
  ("4560127A839", 9),
  ("94560127A38", 9),
  ("8945601273A", 11),
  ("9456012738A", 11),
  ("4560127389A", 9),
  ("A4560127398", 11),
  ("456012739A8", 11),
  ("56012739A48", 9),
  ("8560127394A", 11),
  ("5601273948A", 11),
  ("6012739485A", 11),
  ("0127394856A", 11),
  ("1273948560A", 11),
  ("2739485601A", 11),
  ("7394856012A", 11)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 16 := by decide

theorem based04 : basedOnCheck (List.range 11) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("5607192834A", 11)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("3948560127A", 11)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("3948560127A", 11),
  ("9485601273A", 9),
  ("A9485601237", 11),
  ("948560123A7", 11),
  ("48560123A97", 9),
  ("7485601239A", 11),
  ("4856012397A", 11),
  ("8560123974A", 9),
  ("A8560123947", 9),
  ("7A856012349", 11),
  ("A8560123479", 11),
  ("856012347A9", 11),
  ("56012347A89", 11),
  ("6012347A859", 9),
  ("96012347A58", 9),
  ("8960123475A", 11),
  ("9601234758A", 11),
  ("6012347589A", 9),
  ("A6012347598", 11),
  ("601234759A8", 11),
  ("01234759A68", 9),
  ("8012347596A", 11),
  ("0123475968A", 11),
  ("1234759680A", 11),
  ("2347596801A", 11),
  ("3475968012A", 11),
  ("4759680123A", 11),
  ("7596801234A", 11),
  ("5968012347A", 11),
  ("9680123475A", 9),
  ("A9680123457", 11),
  ("968012345A7", 11)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 18 := by decide

theorem based05 : basedOnCheck (List.range 11) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("3948560127A", 11)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("68012345A97", 9)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("68012345A97", 9),
  ("7680123459A", 11),
  ("6801234597A", 11),
  ("8012345976A", 9),
  ("A8012345967", 9),
  ("7A801234569", 11),
  ("A8012345679", 11),
  ("801234567A9", 11),
  ("01234567A89", 9),
  ("9012345678A", 11)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 10 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 8 := by decide

theorem based06 : basedOnCheck (List.range 11) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("68012345A97", 9)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("0123456789A", 9)) = true := by rfl

def encoded : List (String × Nat) :=
  encoded00 ++
  encoded01 ++
  encoded02 ++
  encoded03 ++
  encoded04 ++
  encoded05 ++
  encoded06

def rows : List (Row Nat) := encoded.map (decodeRow 12)

theorem rows_blocks : rows =
  rows00 ++
  rows01 ++
  rows02 ++
  rows03 ++
  rows04 ++
  rows05 ++
  rows06 := by
  simp only [rows, encoded, List.map_append, rows00, rows01, rows02, rows03, rows04, rows05, rows06]

theorem rows_length : rows.length = 202 := by
  simp only [rows_blocks, List.length_append, length00, length01, length02, length03, length04, length05, length06, Nat.reduceAdd]

theorem rows_charge : (rows.map Row.charge).sum = 116 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 11) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, Bool.and_self]

def suffix06 : List (Row Nat) := rows06

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("68012345A97", 9)) :=
  head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("0123456789A", 9)) :=
  pathRunsToCheck_sound checked06

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("3948560127A", 11)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("0123456789A", 9)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("5607192834A", 11)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("0123456789A", 9)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("12345769A08", 9)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("0123456789A", 9)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("9560123748A", 11)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("0123456789A", 9)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("23456017A89", 11)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("0123456789A", 9)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("80A12345679", 11)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("0123456789A", 9)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("80A12345679", 11)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("0123456789A", 9)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.BlockF0Parts.C01
