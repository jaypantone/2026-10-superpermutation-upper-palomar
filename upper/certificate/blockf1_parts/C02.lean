module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original BlockF1 rows 1024 through 1329.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.BlockF1Parts.C02
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("23845670A19", 11),
  ("3845670A129", 11),
  ("845670A1239", 11),
  ("45670A12389", 11),
  ("5670A123849", 9),
  ("95670A12348", 11),
  ("5670A123498", 11),
  ("670A1234958", 9),
  ("8670A123459", 11),
  ("670A1234589", 11),
  ("70A12345869", 11),
  ("0A123458679", 11),
  ("A1234586709", 9),
  ("9A123458607", 11),
  ("A1234586097", 11),
  ("123458609A7", 11),
  ("23458609A17", 9),
  ("7234586091A", 9),
  ("A7234586019", 11),
  ("723458601A9", 11),
  ("23458601A79", 11),
  ("3458601A729", 11),
  ("458601A7239", 11),
  ("58601A72349", 11),
  ("8601A723459", 11),
  ("601A7234589", 11),
  ("01A72345869", 9),
  ("901A7234568", 11),
  ("01A72345698", 11),
  ("1A723456908", 9),
  ("81A72345609", 11),
  ("1A723456089", 11)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 14 := by decide

theorem based00 : basedOnCheck (List.range 11) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("23845670A19", 11)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("A7234560819", 11)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("A7234560819", 11),
  ("723456081A9", 11),
  ("23456081A79", 11),
  ("3456081A729", 9),
  ("93456081A27", 11),
  ("3456081A297", 11),
  ("456081A2937", 9),
  ("7456081A239", 11),
  ("456081A2379", 11),
  ("56081A23749", 11),
  ("6081A237459", 11),
  ("081A2374569", 11),
  ("81A23745609", 11),
  ("1A237456089", 11),
  ("A2374560819", 9),
  ("9A237456018", 11),
  ("A2374560198", 11),
  ("237456019A8", 11),
  ("37456019A28", 9),
  ("8374560192A", 9),
  ("A8374560129", 11),
  ("837456012A9", 11),
  ("37456012A89", 11),
  ("7456012A839", 11),
  ("456012A8379", 11),
  ("56012A83749", 9),
  ("956012A8347", 11),
  ("56012A83497", 11),
  ("6012A834957", 9),
  ("76012A83459", 11),
  ("6012A834579", 11),
  ("012A8345769", 11)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 14 := by decide

theorem based01 : basedOnCheck (List.range 11) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("A7234560819", 11)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("12A83457609", 11)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("12A83457609", 11),
  ("2A834576019", 11),
  ("A8345760129", 11),
  ("834576012A9", 11),
  ("34576012A89", 11),
  ("4576012A839", 9),
  ("94576012A38", 11),
  ("4576012A398", 11),
  ("576012A3948", 9),
  ("8576012A349", 11),
  ("576012A3489", 11),
  ("76012A34859", 11),
  ("6012A348579", 11),
  ("012A3485769", 9),
  ("9012A348567", 11),
  ("012A3485697", 11),
  ("12A34856907", 9),
  ("712A3485609", 11),
  ("12A34856079", 11),
  ("2A348560719", 11),
  ("A3485607129", 11),
  ("348560712A9", 11),
  ("48560712A39", 11),
  ("8560712A349", 11),
  ("560712A3489", 11),
  ("60712A34859", 9),
  ("960712A3458", 11),
  ("60712A34598", 11),
  ("0712A345968", 9),
  ("80712A34569", 11),
  ("0712A345689", 11),
  ("712A3456809", 11)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 12 := by decide

theorem based02 : basedOnCheck (List.range 11) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("12A83457609", 11)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("12A34568079", 11)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("12A34568079", 11),
  ("2A345680719", 9),
  ("92A34568017", 11),
  ("2A345680197", 11),
  ("A3456801927", 9),
  ("7A345680129", 11),
  ("A3456801279", 11),
  ("345680127A9", 11),
  ("45680127A39", 11),
  ("5680127A349", 11),
  ("680127A3459", 11),
  ("80127A34569", 11),
  ("0127A345689", 11),
  ("127A3456809", 9),
  ("9127A345608", 11),
  ("127A3456098", 11),
  ("27A34560918", 9),
  ("827A3456019", 11),
  ("27A34560189", 11),
  ("7A345601829", 11),
  ("A3456018279", 11),
  ("345601827A9", 11),
  ("45601827A39", 9),
  ("9456018273A", 9),
  ("A9456018237", 11),
  ("945601823A7", 11),
  ("45601823A97", 11),
  ("5601823A947", 9),
  ("75601823A49", 11),
  ("5601823A479", 11),
  ("601823A4759", 11),
  ("01823A47569", 11)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 14 := by decide

theorem based03 : basedOnCheck (List.range 11) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("12A34568079", 11)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("1823A475609", 11)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("1823A475609", 11),
  ("823A4756019", 11),
  ("23A47560189", 11),
  ("3A475601829", 9),
  ("93A47560128", 11),
  ("3A475601298", 11),
  ("A4756012938", 9),
  ("8A475601239", 11),
  ("A4756012389", 11),
  ("475601238A9", 11),
  ("75601238A49", 11),
  ("5601238A479", 11),
  ("601238A4759", 9),
  ("9601238A457", 11),
  ("601238A4597", 11),
  ("01238A45967", 9),
  ("701238A4569", 11),
  ("01238A45679", 11),
  ("1238A456709", 11),
  ("238A4567019", 11),
  ("38A45670129", 11),
  ("8A456701239", 11),
  ("A4567012389", 11),
  ("456701238A9", 11),
  ("56701238A49", 9),
  ("9567012384A", 9),
  ("A9567012348", 11),
  ("956701234A8", 11),
  ("56701234A98", 11),
  ("6701234A958", 9),
  ("86701234A59", 11),
  ("6701234A589", 11)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 14 := by decide

theorem based04 : basedOnCheck (List.range 11) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("1823A475609", 11)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("701234A5869", 11)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("701234A5869", 11),
  ("01234A58679", 11),
  ("1234A586709", 9),
  ("91234A58607", 11),
  ("1234A586097", 11),
  ("234A5860917", 9),
  ("7234A586019", 11),
  ("234A5860179", 11),
  ("34A58601729", 11),
  ("4A586017239", 11),
  ("A5860172349", 11),
  ("586017234A9", 11),
  ("86017234A59", 11),
  ("6017234A589", 11),
  ("017234A5869", 9),
  ("9017234A568", 11),
  ("017234A5698", 11),
  ("17234A56908", 9),
  ("817234A5609", 11),
  ("17234A56089", 11),
  ("7234A560819", 11),
  ("234A5608179", 11),
  ("34A56081729", 9),
  ("934A5608127", 11),
  ("34A56081297", 11),
  ("4A560812937", 9),
  ("74A56081239", 11),
  ("4A560812379", 11),
  ("A5608123749", 11),
  ("560812374A9", 11),
  ("60812374A59", 11),
  ("0812374A569", 11)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 12 := by decide

theorem based05 : basedOnCheck (List.range 11) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("701234A5869", 11)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("812374A5609", 11)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("812374A5609", 11),
  ("12374A56089", 11),
  ("2374A560819", 9),
  ("92374A56018", 11),
  ("2374A560198", 11),
  ("374A5601928", 9),
  ("8374A560129", 11),
  ("374A5601289", 11),
  ("74A56012839", 11),
  ("4A560128379", 11),
  ("A5601283749", 9),
  ("9A560128347", 11),
  ("A5601283497", 11),
  ("560128349A7", 11),
  ("60128349A57", 9),
  ("7601283495A", 9),
  ("A7601283459", 11),
  ("760128345A9", 11),
  ("60128345A79", 11),
  ("0128345A769", 11),
  ("128345A7609", 11),
  ("28345A76019", 11),
  ("8345A760129", 11),
  ("345A7601289", 11),
  ("45A76012839", 9),
  ("945A7601238", 11),
  ("45A76012398", 11),
  ("5A760123948", 9),
  ("85A76012349", 11),
  ("5A760123489", 11),
  ("A7601234859", 11),
  ("760123485A9", 11)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 14 := by decide

theorem based06 : basedOnCheck (List.range 11) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("812374A5609", 11)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("60123485A79", 11)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("60123485A79", 11),
  ("0123485A769", 9),
  ("90123485A67", 11),
  ("0123485A697", 11),
  ("123485A6907", 9),
  ("7123485A609", 11),
  ("123485A6079", 11),
  ("23485A60719", 11),
  ("3485A607129", 11),
  ("485A6071239", 11),
  ("85A60712349", 11),
  ("5A607123489", 11),
  ("A6071234859", 9),
  ("9A607123458", 11),
  ("A6071234598", 11),
  ("607123459A8", 11),
  ("07123459A68", 9),
  ("8071234596A", 9),
  ("A8071234569", 11),
  ("807123456A9", 11),
  ("07123456A89", 11),
  ("7123456A809", 11),
  ("123456A8079", 11),
  ("23456A80719", 9),
  ("923456A8017", 11),
  ("23456A80197", 11),
  ("3456A801927", 9),
  ("73456A80129", 11),
  ("3456A801279", 11),
  ("456A8012739", 11),
  ("56A80127349", 11),
  ("6A801273459", 11)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 14 := by decide

theorem based07 : basedOnCheck (List.range 11) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("60123485A79", 11)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("A8012734569", 11)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("A8012734569", 11),
  ("801273456A9", 11),
  ("01273456A89", 11),
  ("1273456A809", 9),
  ("91273456A08", 11),
  ("1273456A098", 11),
  ("273456A0918", 9),
  ("8273456A019", 11),
  ("273456A0189", 11),
  ("73456A01829", 11),
  ("3456A018279", 11),
  ("456A0182739", 9),
  ("9456A018237", 11),
  ("456A0182397", 11),
  ("56A01823947", 9),
  ("756A0182349", 11),
  ("56A01823479", 11),
  ("6A018234759", 11),
  ("A0182347569", 11),
  ("018234756A9", 11),
  ("18234756A09", 11),
  ("8234756A019", 11),
  ("234756A0189", 11),
  ("34756A01829", 9),
  ("934756A0128", 11),
  ("34756A01298", 11),
  ("4756A012938", 9),
  ("84756A01239", 11),
  ("4756A012389", 11),
  ("756A0123849", 11),
  ("56A01238479", 11),
  ("6A012384759", 9)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 14 := by decide

theorem based08 : basedOnCheck (List.range 11) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("A8012734569", 11)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("96A01238457", 11)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("96A01238457", 11),
  ("6A012384597", 11),
  ("A0123845967", 9),
  ("7A012384569", 11),
  ("A0123845679", 11),
  ("012384567A9", 11),
  ("12384567A09", 11),
  ("2384567A019", 11),
  ("384567A0129", 11),
  ("84567A01239", 11),
  ("4567A012389", 11),
  ("567A0123849", 9),
  ("9567A012348", 11),
  ("567A0123498", 11),
  ("67A01234958", 9),
  ("867A0123459", 11),
  ("67A01234589", 11),
  ("7A012345869", 11)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 18 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 6 := by decide

theorem based09 : basedOnCheck (List.range 11) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("96A01238457", 11)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("A0123458679", 11)) = true := by rfl

def encoded : List (String × Nat) :=
  encoded00 ++
  encoded01 ++
  encoded02 ++
  encoded03 ++
  encoded04 ++
  encoded05 ++
  encoded06 ++
  encoded07 ++
  encoded08 ++
  encoded09

def rows : List (Row Nat) := encoded.map (decodeRow 12)

theorem rows_blocks : rows =
  rows00 ++
  rows01 ++
  rows02 ++
  rows03 ++
  rows04 ++
  rows05 ++
  rows06 ++
  rows07 ++
  rows08 ++
  rows09 := by
  simp only [rows, encoded, List.map_append, rows00, rows01, rows02, rows03, rows04, rows05, rows06, rows07, rows08, rows09]

theorem rows_length : rows.length = 306 := by
  simp only [rows_blocks, List.length_append, length00, length01, length02, length03, length04, length05, length06, length07, length08, length09, Nat.reduceAdd]

theorem rows_charge : (rows.map Row.charge).sum = 128 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, charge08, charge09, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 11) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, based08, based09, Bool.and_self]

def suffix09 : List (Row Nat) := rows09

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("96A01238457", 11)) :=
  head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("A0123458679", 11)) :=
  pathRunsToCheck_sound checked09

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("A8012734569", 11)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("A0123458679", 11)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("60123485A79", 11)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("A0123458679", 11)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("812374A5609", 11)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("A0123458679", 11)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("701234A5869", 11)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("A0123458679", 11)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("1823A475609", 11)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("A0123458679", 11)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("12A34568079", 11)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("A0123458679", 11)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("12A83457609", 11)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("A0123458679", 11)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("A7234560819", 11)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("A0123458679", 11)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("23845670A19", 11)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("A0123458679", 11)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("23845670A19", 11)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("A0123458679", 11)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.BlockF1Parts.C02
