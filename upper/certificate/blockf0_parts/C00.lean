module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original BlockF0 rows 0 through 511.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.BlockF0Parts.C00
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("0123456789A", 9),
  ("A0123456798", 9),
  ("8A012345697", 11),
  ("A0123456987", 9),
  ("7A012345689", 11),
  ("A0123456879", 11),
  ("012345687A9", 9),
  ("901234568A7", 11),
  ("01234568A97", 9),
  ("7012345689A", 9),
  ("A7012345698", 11),
  ("701234569A8", 9),
  ("870123456A9", 11),
  ("70123456A89", 11),
  ("0123456A879", 9),
  ("90123456A78", 11),
  ("0123456A798", 9),
  ("80123456A97", 9),
  ("7801234569A", 9),
  ("A7801234596", 11),
  ("780123459A6", 9),
  ("678012345A9", 11),
  ("78012345A69", 11),
  ("8012345A679", 11),
  ("012345A6789", 11),
  ("12345A67809", 9),
  ("912345A6708", 11),
  ("12345A67098", 9),
  ("812345A6790", 9),
  ("0812345A697", 11),
  ("812345A6907", 9),
  ("7812345A609", 11)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 32 := by decide

theorem based00 : basedOnCheck (List.range 11) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("0123456789A", 9)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("812345A6079", 11)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("812345A6079", 11),
  ("12345A60789", 11),
  ("2345A607819", 9),
  ("92345A60718", 11),
  ("2345A607198", 9),
  ("82345A60791", 9),
  ("182345A6097", 11),
  ("82345A60917", 9),
  ("782345A6019", 11),
  ("82345A60179", 11),
  ("2345A601789", 11),
  ("345A6017829", 9),
  ("9345A601728", 11),
  ("345A6017298", 9),
  ("8345A601792", 9),
  ("28345A60197", 11),
  ("8345A601927", 9),
  ("78345A60129", 11),
  ("8345A601279", 11),
  ("345A6012789", 11),
  ("45A60127839", 9),
  ("945A6012738", 11),
  ("45A60127398", 9),
  ("845A6012793", 9),
  ("3845A601297", 11),
  ("845A6012937", 9),
  ("7845A601239", 11),
  ("845A6012379", 11),
  ("45A60123789", 11),
  ("5A601237849", 9),
  ("95A60123748", 11),
  ("5A601237498", 9)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 28 := by decide

theorem based01 : basedOnCheck (List.range 11) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("812345A6079", 11)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("85A60123794", 9)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("85A60123794", 9),
  ("485A6012397", 11),
  ("85A60123947", 9),
  ("785A6012349", 11),
  ("85A60123479", 11),
  ("5A601234789", 11),
  ("A6012347859", 11),
  ("601234785A9", 9),
  ("960123478A5", 11),
  ("60123478A95", 9),
  ("5601234789A", 9),
  ("A5601234798", 9),
  ("8A560123497", 11),
  ("A5601234987", 9),
  ("7A560123489", 11),
  ("A5601234879", 11),
  ("560123487A9", 9),
  ("956012348A7", 11),
  ("56012348A97", 9),
  ("7560123489A", 9),
  ("A7560123498", 11),
  ("756012349A8", 9),
  ("875601234A9", 11),
  ("75601234A89", 11),
  ("5601234A879", 9),
  ("95601234A78", 11),
  ("5601234A798", 9),
  ("85601234A97", 9),
  ("7856012349A", 9),
  ("A7856012394", 11),
  ("785601239A4", 9),
  ("478560123A9", 11)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 32 := by decide

theorem based02 : basedOnCheck (List.range 11) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("85A60123794", 9)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("78560123A49", 11)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("78560123A49", 11),
  ("8560123A479", 11),
  ("560123A4789", 11),
  ("60123A47859", 9),
  ("960123A4758", 11),
  ("60123A47598", 9),
  ("860123A4795", 9),
  ("5860123A497", 11),
  ("860123A4957", 9),
  ("7860123A459", 11),
  ("860123A4579", 11),
  ("60123A45789", 11),
  ("0123A457869", 9),
  ("90123A45768", 11),
  ("0123A457698", 9),
  ("80123A45796", 9),
  ("680123A4597", 11),
  ("80123A45967", 9),
  ("780123A4569", 11),
  ("80123A45679", 11),
  ("0123A456789", 11),
  ("123A4567809", 9),
  ("9123A456708", 11),
  ("123A4567098", 9),
  ("8123A456790", 9),
  ("08123A45697", 11),
  ("8123A456907", 9),
  ("78123A45609", 11),
  ("8123A456079", 11),
  ("123A4560789", 11),
  ("23A45607819", 9),
  ("923A4560718", 11)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 26 := by decide

theorem based03 : basedOnCheck (List.range 11) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("78560123A49", 11)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("23A45607198", 9)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("23A45607198", 9),
  ("823A4560791", 9),
  ("1823A456097", 11),
  ("823A4560917", 9),
  ("7823A456019", 11),
  ("823A4560179", 11),
  ("23A45601789", 11),
  ("3A456017829", 9),
  ("93A45601728", 11),
  ("3A456017298", 9),
  ("83A45601792", 9),
  ("283A4560197", 11),
  ("83A45601927", 9),
  ("783A4560129", 11),
  ("83A45601279", 11),
  ("3A456012789", 11),
  ("A4560127839", 11),
  ("456012783A9", 9),
  ("945601278A3", 11),
  ("45601278A93", 9),
  ("3456012789A", 9),
  ("A3456012798", 9),
  ("8A345601297", 11),
  ("A3456012987", 9),
  ("7A345601289", 11),
  ("A3456012879", 11),
  ("345601287A9", 9),
  ("934560128A7", 11),
  ("34560128A97", 9),
  ("7345601289A", 9),
  ("A7345601298", 11),
  ("734560129A8", 9)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 32 := by decide

theorem based04 : basedOnCheck (List.range 11) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("23A45607198", 9)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("873456012A9", 11)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("873456012A9", 11),
  ("73456012A89", 11),
  ("3456012A879", 9),
  ("93456012A78", 11),
  ("3456012A798", 9),
  ("83456012A97", 9),
  ("7834560129A", 9),
  ("A7834560192", 11),
  ("783456019A2", 9),
  ("278345601A9", 11),
  ("78345601A29", 11),
  ("8345601A279", 11),
  ("345601A2789", 11),
  ("45601A27839", 9),
  ("945601A2738", 11),
  ("45601A27398", 9),
  ("845601A2793", 9),
  ("3845601A297", 11),
  ("845601A2937", 9),
  ("7845601A239", 11),
  ("845601A2379", 11),
  ("45601A23789", 11),
  ("5601A237849", 9),
  ("95601A23748", 11),
  ("5601A237498", 9),
  ("85601A23794", 9),
  ("485601A2397", 11),
  ("85601A23947", 9),
  ("785601A2349", 11),
  ("85601A23479", 11),
  ("5601A234789", 11),
  ("601A2347859", 9)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 28 := by decide

theorem based05 : basedOnCheck (List.range 11) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("873456012A9", 11)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("9601A234758", 11)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("9601A234758", 11),
  ("601A2347598", 9),
  ("8601A234795", 9),
  ("58601A23497", 11),
  ("8601A234957", 9),
  ("78601A23459", 11),
  ("8601A234579", 11),
  ("601A2345789", 11),
  ("01A23457869", 9),
  ("901A2345768", 11),
  ("01A23457698", 9),
  ("801A2345796", 9),
  ("6801A234597", 11),
  ("801A2345967", 9),
  ("7801A234569", 11),
  ("801A2345679", 11),
  ("01A23456789", 11),
  ("1A234567809", 9),
  ("91A23456708", 11),
  ("1A234567098", 9),
  ("81A23456790", 9),
  ("081A2345697", 11),
  ("81A23456907", 9),
  ("781A2345609", 11),
  ("81A23456079", 11),
  ("1A234560789", 11),
  ("A2345607819", 11),
  ("234560781A9", 9),
  ("923456078A1", 11),
  ("23456078A91", 9),
  ("1234560789A", 9),
  ("A1234560798", 9)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 30 := by decide

theorem based06 : basedOnCheck (List.range 11) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("9601A234758", 11)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("8A123456097", 11)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("8A123456097", 11),
  ("A1234560987", 9),
  ("7A123456089", 11),
  ("A1234560879", 11),
  ("123456087A9", 9),
  ("912345608A7", 11),
  ("12345608A97", 9),
  ("7123456089A", 9),
  ("A7123456098", 11),
  ("712345609A8", 9),
  ("871234560A9", 11),
  ("71234560A89", 11),
  ("1234560A879", 9),
  ("91234560A78", 11),
  ("1234560A798", 9),
  ("81234560A97", 9),
  ("7812345609A", 9),
  ("A7812345690", 11),
  ("781234569A0", 9),
  ("078123456A9", 11),
  ("78123456A09", 11),
  ("8123456A079", 11),
  ("123456A0789", 11),
  ("23456A07819", 9),
  ("923456A0718", 11),
  ("23456A07198", 9),
  ("823456A0791", 9),
  ("1823456A097", 11),
  ("823456A0917", 9),
  ("7823456A019", 11),
  ("823456A0179", 11),
  ("23456A01789", 11)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 28 := by decide

theorem based07 : basedOnCheck (List.range 11) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("8A123456097", 11)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("3456A017829", 9)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("3456A017829", 9),
  ("93456A01728", 11),
  ("3456A017298", 9),
  ("83456A01792", 9),
  ("283456A0197", 11),
  ("83456A01927", 9),
  ("783456A0129", 11),
  ("83456A01279", 11),
  ("3456A012789", 11),
  ("456A0127839", 9),
  ("9456A012738", 11),
  ("456A0127398", 9),
  ("8456A012793", 9),
  ("38456A01297", 11),
  ("8456A012937", 9),
  ("78456A01239", 11),
  ("8456A012379", 11),
  ("456A0123789", 11),
  ("56A01237849", 9),
  ("956A0123748", 11),
  ("56A01237498", 9),
  ("856A0123794", 9),
  ("4856A012397", 11),
  ("856A0123947", 9),
  ("7856A012349", 11),
  ("856A0123479", 11),
  ("56A01234789", 11),
  ("6A012347859", 9),
  ("96A01234758", 11),
  ("6A012347598", 9),
  ("86A01234795", 9),
  ("586A0123497", 11)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 30 := by decide

theorem based08 : basedOnCheck (List.range 11) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("3456A017829", 9)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("86A01234957", 9)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("86A01234957", 9),
  ("786A0123459", 11),
  ("86A01234579", 11),
  ("6A012345789", 11),
  ("A0123457869", 11),
  ("012345786A9", 9),
  ("901234578A6", 11),
  ("01234578A96", 9),
  ("6012345789A", 9),
  ("A6012345798", 9),
  ("8A601234597", 11),
  ("A6012345987", 9),
  ("7A601234589", 11),
  ("A6012345879", 11),
  ("601234587A9", 9),
  ("960123458A7", 11),
  ("60123458A97", 9),
  ("7601234589A", 9),
  ("A7601234598", 11),
  ("760123459A8", 9),
  ("876012345A9", 11),
  ("76012345A89", 11),
  ("6012345A879", 9),
  ("96012345A78", 11),
  ("6012345A798", 9),
  ("86012345A97", 9),
  ("7860123459A", 9),
  ("A7860123495", 11),
  ("786012349A5", 9),
  ("578601234A9", 11),
  ("78601234A59", 11),
  ("8601234A579", 11)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 30 := by decide

theorem based09 : basedOnCheck (List.range 11) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("86A01234957", 9)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("601234A5789", 11)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("601234A5789", 11),
  ("01234A57869", 9),
  ("901234A5768", 11),
  ("01234A57698", 9),
  ("801234A5796", 9),
  ("6801234A597", 11),
  ("801234A5967", 9),
  ("7801234A569", 11),
  ("801234A5679", 11),
  ("01234A56789", 11),
  ("1234A567809", 9),
  ("91234A56708", 11),
  ("1234A567098", 9),
  ("81234A56790", 9),
  ("081234A5697", 11),
  ("81234A56907", 9),
  ("781234A5609", 11),
  ("81234A56079", 11),
  ("1234A560789", 11),
  ("234A5607819", 9),
  ("9234A560718", 11),
  ("234A5607198", 9),
  ("8234A560791", 9),
  ("18234A56097", 11),
  ("8234A560917", 9),
  ("78234A56019", 11),
  ("8234A560179", 11),
  ("234A5601789", 11),
  ("34A56017829", 9),
  ("934A5601728", 11),
  ("34A56017298", 9),
  ("834A5601792", 9)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 30 := by decide

theorem based10 : basedOnCheck (List.range 11) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("601234A5789", 11)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("2834A560197", 11)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("2834A560197", 11),
  ("834A5601927", 9),
  ("7834A560129", 11),
  ("834A5601279", 11),
  ("34A56012789", 11),
  ("4A560127839", 9),
  ("94A56012738", 11),
  ("4A560127398", 9),
  ("84A56012793", 9),
  ("384A5601297", 11),
  ("84A56012937", 9),
  ("784A5601239", 11),
  ("84A56012379", 11),
  ("4A560123789", 11),
  ("A5601237849", 11),
  ("560123784A9", 9),
  ("956012378A4", 11),
  ("56012378A94", 9),
  ("4560123789A", 9),
  ("A4560123798", 9),
  ("8A456012397", 11),
  ("A4560123987", 9),
  ("7A456012389", 11),
  ("A4560123879", 11),
  ("456012387A9", 9),
  ("945601238A7", 11),
  ("45601238A97", 9),
  ("7456012389A", 9),
  ("A7456012398", 11),
  ("745601239A8", 9),
  ("874560123A9", 11),
  ("74560123A89", 11)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 28 := by decide

theorem based11 : basedOnCheck (List.range 11) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("2834A560197", 11)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("4560123A879", 9)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("4560123A879", 9),
  ("94560123A78", 11),
  ("4560123A798", 9),
  ("84560123A97", 9),
  ("7845601239A", 9),
  ("A7845601293", 11),
  ("784560129A3", 9),
  ("378456012A9", 11),
  ("78456012A39", 11),
  ("8456012A379", 11),
  ("456012A3789", 11),
  ("56012A37849", 9),
  ("956012A3748", 11),
  ("56012A37498", 9),
  ("856012A3794", 9),
  ("4856012A397", 11),
  ("856012A3947", 9),
  ("7856012A349", 11),
  ("856012A3479", 11),
  ("56012A34789", 11),
  ("6012A347859", 9),
  ("96012A34758", 11),
  ("6012A347598", 9),
  ("86012A34795", 9),
  ("586012A3497", 11),
  ("86012A34957", 9),
  ("786012A3459", 11),
  ("86012A34579", 11),
  ("6012A345789", 11),
  ("012A3457869", 9),
  ("9012A345768", 11),
  ("012A3457698", 9)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 30 := by decide

theorem based12 : basedOnCheck (List.range 11) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("4560123A879", 9)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("8012A345796", 9)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("8012A345796", 9),
  ("68012A34597", 11),
  ("8012A345967", 9),
  ("78012A34569", 11),
  ("8012A345679", 11),
  ("012A3456789", 11),
  ("12A34567809", 9),
  ("912A3456708", 11),
  ("12A34567098", 9),
  ("812A3456790", 9),
  ("0812A345697", 11),
  ("812A3456907", 9),
  ("7812A345609", 11),
  ("812A3456079", 11),
  ("12A34560789", 11),
  ("2A345607819", 9),
  ("92A34560718", 11),
  ("2A345607198", 9),
  ("82A34560791", 9),
  ("182A3456097", 11),
  ("82A34560917", 9),
  ("782A3456019", 11),
  ("82A34560179", 11),
  ("2A345601789", 11),
  ("A3456017829", 11),
  ("345601782A9", 9),
  ("934560178A2", 11),
  ("34560178A92", 9),
  ("2345601789A", 9),
  ("A2345601798", 9),
  ("8A234560197", 11),
  ("A2345601987", 9)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 30 := by decide

theorem based13 : basedOnCheck (List.range 11) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("8012A345796", 9)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("7A234560189", 11)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("7A234560189", 11),
  ("A2345601879", 11),
  ("234560187A9", 9),
  ("923456018A7", 11),
  ("23456018A97", 9),
  ("7234560189A", 9),
  ("A7234560198", 11),
  ("723456019A8", 9),
  ("872345601A9", 11),
  ("72345601A89", 11),
  ("2345601A879", 9),
  ("92345601A78", 11),
  ("2345601A798", 9),
  ("82345601A97", 9),
  ("7823456019A", 9),
  ("A7823456091", 11),
  ("782345609A1", 9),
  ("178234560A9", 11),
  ("78234560A19", 11),
  ("8234560A179", 11),
  ("234560A1789", 11),
  ("34560A17829", 9),
  ("934560A1728", 11),
  ("34560A17298", 9),
  ("834560A1792", 9),
  ("2834560A197", 11),
  ("834560A1927", 9),
  ("7834560A129", 11),
  ("834560A1279", 11),
  ("34560A12789", 11),
  ("4560A127839", 9),
  ("94560A12738", 11)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 28 := by decide

theorem based14 : basedOnCheck (List.range 11) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("7A234560189", 11)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("4560A127398", 9)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("4560A127398", 9),
  ("84560A12793", 9),
  ("384560A1297", 11),
  ("84560A12937", 9),
  ("784560A1239", 11),
  ("84560A12379", 11),
  ("4560A123789", 11),
  ("560A1237849", 9),
  ("9560A123748", 11),
  ("560A1237498", 9),
  ("8560A123794", 9),
  ("48560A12397", 11),
  ("8560A123947", 9),
  ("78560A12349", 11),
  ("8560A123479", 11),
  ("560A1234789", 11),
  ("60A12347859", 9),
  ("960A1234758", 11),
  ("60A12347598", 9),
  ("860A1234795", 9),
  ("5860A123497", 11),
  ("860A1234957", 9),
  ("7860A123459", 11),
  ("860A1234579", 11),
  ("60A12345789", 11),
  ("0A123457869", 9),
  ("90A12345768", 11),
  ("0A123457698", 9),
  ("80A12345796", 9),
  ("680A1234597", 11),
  ("80A12345967", 9),
  ("780A1234569", 11)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 32 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 30 := by decide

theorem based15 : basedOnCheck (List.range 11) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("4560A127398", 9)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("80A12345679", 11)) = true := by rfl

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
  encoded09 ++
  encoded10 ++
  encoded11 ++
  encoded12 ++
  encoded13 ++
  encoded14 ++
  encoded15

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
  rows09 ++
  rows10 ++
  rows11 ++
  rows12 ++
  rows13 ++
  rows14 ++
  rows15 := by
  simp only [rows, encoded, List.map_append, rows00, rows01, rows02, rows03, rows04, rows05, rows06, rows07, rows08, rows09, rows10, rows11, rows12, rows13, rows14, rows15]

theorem rows_length : rows.length = 512 := by
  simp only [rows_blocks, List.length_append, length00, length01, length02, length03, length04, length05, length06, length07, length08, length09, length10, length11, length12, length13, length14, length15, Nat.reduceAdd]

theorem rows_charge : (rows.map Row.charge).sum = 472 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, charge08, charge09, charge10, charge11, charge12, charge13, charge14, charge15, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 11) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, based08, based09, based10, based11, based12, based13, based14, based15, Bool.and_self]

def suffix15 : List (Row Nat) := rows15

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("4560A127398", 9)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("7A234560189", 11)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("8012A345796", 9)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("4560123A879", 9)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("2834A560197", 11)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("601234A5789", 11)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("86A01234957", 9)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("3456A017829", 9)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("8A123456097", 11)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("9601A234758", 11)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("873456012A9", 11)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("23A45607198", 9)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("78560123A49", 11)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("85A60123794", 9)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("812345A6079", 11)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("0123456789A", 9)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("80A12345679", 11)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("0123456789A", 9)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("80A12345679", 11)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.BlockF0Parts.C00
