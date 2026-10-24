module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original BlockF2 rows 1536 through 2029.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.BlockF2Parts.C03
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("345A6091287", 11),
  ("45A60912837", 9),
  ("745A6091238", 11),
  ("45A60912378", 11),
  ("5A609123748", 11),
  ("A6091237458", 11),
  ("609123745A8", 9),
  ("860912374A5", 9),
  ("586091237A4", 9),
  ("458609123A7", 11),
  ("58609123A47", 9),
  ("7586091234A", 11),
  ("5860912347A", 11),
  ("8609123475A", 11),
  ("6091234758A", 9),
  ("A6091234785", 9),
  ("5A609123487", 11),
  ("A6091234857", 9),
  ("7A609123458", 11),
  ("A6091234578", 11),
  ("609123457A8", 11),
  ("09123457A68", 11),
  ("9123457A608", 11),
  ("123457A6098", 11),
  ("23457A60918", 9),
  ("823457A6019", 11),
  ("23457A60189", 11),
  ("3457A601829", 11),
  ("457A6018239", 11),
  ("57A60182349", 11),
  ("7A601823459", 11),
  ("A6018234579", 11)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 18 := by decide

theorem based00 : basedOnCheck (List.range 11) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("345A6091287", 11)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("601823457A9", 11)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("601823457A9", 11),
  ("01823457A69", 9),
  ("9018234576A", 9),
  ("A9018234567", 11),
  ("901823456A7", 11),
  ("01823456A97", 11),
  ("1823456A907", 11),
  ("823456A9017", 11),
  ("23456A90187", 11),
  ("3456A901827", 9),
  ("73456A90128", 11),
  ("3456A901278", 11),
  ("456A9012738", 9),
  ("8456A901237", 11),
  ("456A9012387", 11),
  ("56A90123847", 9),
  ("756A9012348", 11),
  ("56A90123478", 11),
  ("6A901234758", 11),
  ("A9012347568", 11),
  ("901234756A8", 11),
  ("01234756A98", 11),
  ("1234756A908", 9),
  ("81234756A09", 11),
  ("1234756A089", 11),
  ("234756A0819", 11),
  ("34756A08129", 11),
  ("4756A081239", 11),
  ("756A0812349", 11),
  ("56A08123479", 11),
  ("6A081234759", 9),
  ("96A08123457", 11)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 14 := by decide

theorem based01 : basedOnCheck (List.range 11) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("601823457A9", 11)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("6A081234597", 11)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("6A081234597", 11),
  ("A0812345967", 11),
  ("081234596A7", 11),
  ("81234596A07", 11),
  ("1234596A087", 11),
  ("234596A0817", 9),
  ("7234596A018", 11),
  ("234596A0178", 11),
  ("34596A01728", 9),
  ("834596A0127", 11),
  ("34596A01287", 11),
  ("4596A012837", 9),
  ("74596A01238", 11),
  ("4596A012378", 11),
  ("596A0123748", 11),
  ("96A01237458", 11),
  ("6A012374598", 11),
  ("A0123745968", 9),
  ("8A012374569", 11),
  ("A0123745689", 11),
  ("012374568A9", 11),
  ("12374568A09", 11),
  ("2374568A019", 11),
  ("374568A0129", 11),
  ("74568A01239", 11),
  ("4568A012379", 11),
  ("568A0123749", 9),
  ("9568A012347", 11),
  ("568A0123497", 11),
  ("68A01234957", 11),
  ("8A012349567", 11),
  ("A0123495687", 11)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 10 := by decide

theorem based02 : basedOnCheck (List.range 11) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("6A081234597", 11)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("012349568A7", 11)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("012349568A7", 11),
  ("12349568A07", 9),
  ("7123495680A", 9),
  ("A7123495608", 11),
  ("712349560A8", 11),
  ("12349560A78", 11),
  ("2349560A718", 9),
  ("82349560A17", 11),
  ("2349560A187", 9),
  ("72349560A81", 9),
  ("1723495608A", 11),
  ("7234956081A", 11),
  ("2349560817A", 11),
  ("3495608172A", 9),
  ("A3495608127", 11),
  ("349560812A7", 9),
  ("734956081A2", 9),
  ("273495608A1", 9),
  ("127349560A8", 11),
  ("27349560A18", 11),
  ("7349560A128", 11),
  ("349560A1278", 11),
  ("49560A12738", 11),
  ("9560A127348", 11),
  ("560A1273498", 11),
  ("60A12734958", 9),
  ("860A1273459", 11),
  ("60A12734589", 11),
  ("0A127345869", 11),
  ("A1273458609", 11),
  ("127345860A9", 11),
  ("27345860A19", 11)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 20 := by decide

theorem based03 : basedOnCheck (List.range 11) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("012349568A7", 11)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("7345860A129", 11)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("7345860A129", 11),
  ("345860A1279", 11),
  ("45860A12739", 9),
  ("945860A1237", 11),
  ("45860A12397", 11),
  ("5860A123947", 11),
  ("860A1239457", 11),
  ("60A12394587", 11),
  ("0A123945867", 9),
  ("70A12394568", 11),
  ("0A123945678", 11),
  ("A1239456708", 9),
  ("8A123945607", 11),
  ("A1239456087", 11),
  ("123945608A7", 11),
  ("23945608A17", 9),
  ("7239456081A", 9),
  ("A7239456018", 11),
  ("723945601A8", 11),
  ("23945601A78", 11),
  ("3945601A728", 11),
  ("945601A7238", 11),
  ("45601A72398", 11),
  ("5601A723948", 9),
  ("85601A72349", 11),
  ("5601A723489", 11),
  ("601A7234859", 11),
  ("01A72348569", 11),
  ("1A723485609", 11),
  ("A7234856019", 11),
  ("723485601A9", 11),
  ("23485601A79", 11)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 12 := by decide

theorem based04 : basedOnCheck (List.range 11) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("7345860A129", 11)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("3485601A729", 9)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("3485601A729", 9),
  ("93485601A27", 11),
  ("3485601A297", 11),
  ("485601A2937", 11),
  ("85601A29347", 11),
  ("5601A293487", 11),
  ("601A2934857", 9),
  ("7601A293458", 11),
  ("601A2934578", 11),
  ("01A29345768", 9),
  ("801A2934567", 11),
  ("01A29345687", 11),
  ("1A293456807", 9),
  ("71A29345608", 11),
  ("1A293456078", 11),
  ("A2934560718", 11),
  ("293456071A8", 11),
  ("93456071A28", 11),
  ("3456071A298", 11),
  ("456071A2938", 9),
  ("8456071A239", 11),
  ("456071A2389", 11),
  ("56071A23849", 11),
  ("6071A238459", 11),
  ("071A2384569", 11),
  ("71A23845609", 11),
  ("1A238456079", 11),
  ("A2384560719", 9),
  ("9A238456017", 11),
  ("A2384560197", 11),
  ("238456019A7", 11),
  ("38456019A27", 11)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 12 := by decide

theorem based05 : basedOnCheck (List.range 11) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("3485601A729", 9)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("8456019A237", 11)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("8456019A237", 11),
  ("456019A2387", 11),
  ("56019A23847", 9),
  ("756019A2348", 11),
  ("56019A23478", 11),
  ("6019A234758", 9),
  ("86019A23457", 11),
  ("6019A234587", 11),
  ("019A2345867", 9),
  ("7019A234568", 11),
  ("019A2345678", 11),
  ("19A23456708", 11),
  ("9A234567018", 11),
  ("A2345670198", 11),
  ("234567019A8", 11),
  ("34567019A28", 9),
  ("8345670192A", 9),
  ("A8345670129", 11),
  ("834567012A9", 11),
  ("34567012A89", 11),
  ("4567012A839", 11),
  ("567012A8349", 11),
  ("67012A83459", 11),
  ("7012A834569", 11),
  ("012A8345679", 11),
  ("12A83456709", 9),
  ("912A8345607", 11),
  ("12A83456097", 11),
  ("2A834560917", 11),
  ("A8345609127", 11),
  ("834560912A7", 11),
  ("34560912A87", 11)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 12 := by decide

theorem based06 : basedOnCheck (List.range 11) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("8456019A237", 11)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("4560912A837", 9)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("4560912A837", 9),
  ("74560912A38", 11),
  ("4560912A378", 9),
  ("84560912A73", 9),
  ("3845609127A", 11),
  ("8456091273A", 11),
  ("4560912738A", 11),
  ("5609127384A", 9),
  ("A5609127348", 11),
  ("560912734A8", 9),
  ("856091273A4", 9),
  ("485609127A3", 9),
  ("348560912A7", 11),
  ("48560912A37", 11),
  ("8560912A347", 11),
  ("560912A3487", 11),
  ("60912A34857", 9),
  ("760912A3458", 11),
  ("60912A34578", 11),
  ("0912A345768", 11),
  ("912A3457608", 11),
  ("12A34576098", 11),
  ("2A345760918", 9),
  ("82A34576019", 11),
  ("2A345760189", 11),
  ("A3457601829", 11),
  ("345760182A9", 11),
  ("45760182A39", 11),
  ("5760182A349", 11),
  ("760182A3459", 11),
  ("60182A34579", 11),
  ("0182A345769", 9)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 20 := by decide

theorem based07 : basedOnCheck (List.range 11) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("4560912A837", 9)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("90182A34567", 11)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("90182A34567", 11),
  ("0182A345697", 11),
  ("182A3456907", 11),
  ("82A34569017", 11),
  ("2A345690187", 11),
  ("A3456901827", 9),
  ("7A345690128", 11),
  ("A3456901278", 11),
  ("345690127A8", 11),
  ("45690127A38", 9),
  ("8456901273A", 9),
  ("A8456901237", 11),
  ("845690123A7", 11),
  ("45690123A87", 11),
  ("5690123A847", 9),
  ("75690123A48", 11),
  ("5690123A478", 11),
  ("690123A4758", 11),
  ("90123A47568", 11),
  ("0123A475698", 11),
  ("123A4756908", 9),
  ("8123A475609", 11),
  ("123A4756089", 11),
  ("23A47560819", 11),
  ("3A475608129", 11),
  ("A4756081239", 11),
  ("475608123A9", 11),
  ("75608123A49", 11),
  ("5608123A479", 11),
  ("608123A4759", 9),
  ("9608123A457", 11),
  ("608123A4597", 11)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 12 := by decide

theorem based08 : basedOnCheck (List.range 11) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("90182A34567", 11)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("08123A45967", 11)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("08123A45967", 11),
  ("8123A459607", 11),
  ("123A4596087", 11),
  ("23A45960817", 9),
  ("723A4596018", 11),
  ("23A45960178", 11),
  ("3A459601728", 11),
  ("A4596017238", 11),
  ("459601723A8", 9),
  ("845960172A3", 9),
  ("384596017A2", 9),
  ("238459601A7", 11),
  ("38459601A27", 9),
  ("7384596012A", 11),
  ("3845960127A", 11),
  ("8459601273A", 11),
  ("4596012738A", 9),
  ("A4596012783", 9),
  ("3A459601287", 11),
  ("A4596012837", 9),
  ("7A459601238", 11),
  ("A4596012378", 11),
  ("459601237A8", 11),
  ("59601237A48", 11),
  ("9601237A458", 11),
  ("601237A4598", 11),
  ("01237A45968", 9),
  ("801237A4569", 11),
  ("01237A45689", 11),
  ("1237A456809", 11),
  ("237A4568019", 11),
  ("37A45680129", 11)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 18 := by decide

theorem based09 : basedOnCheck (List.range 11) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("08123A45967", 11)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("7A456801239", 11)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("7A456801239", 11),
  ("A4568012379", 11),
  ("456801237A9", 11),
  ("56801237A49", 9),
  ("9568012374A", 9),
  ("A9568012347", 11),
  ("956801234A7", 11),
  ("56801234A97", 11),
  ("6801234A957", 11),
  ("801234A9567", 11),
  ("01234A95687", 11),
  ("1234A956807", 9),
  ("71234A95608", 11),
  ("1234A956078", 11),
  ("234A9560718", 9),
  ("8234A956017", 11),
  ("234A9560187", 11),
  ("34A95601827", 9),
  ("734A9560128", 11),
  ("34A95601278", 11),
  ("4A956012738", 11),
  ("A9560127348", 11),
  ("956012734A8", 11),
  ("56012734A98", 11),
  ("6012734A958", 9),
  ("86012734A59", 11),
  ("6012734A589", 11),
  ("012734A5869", 11),
  ("12734A58609", 11),
  ("2734A586019", 11),
  ("734A5860129", 11),
  ("34A58601279", 11)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 12 := by decide

theorem based10 : basedOnCheck (List.range 11) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("7A456801239", 11)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("4A586012739", 9)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("4A586012739", 9),
  ("94A58601237", 11),
  ("4A586012397", 11),
  ("A5860123947", 11),
  ("586012394A7", 11),
  ("86012394A57", 11),
  ("6012394A587", 11),
  ("012394A5867", 9),
  ("7012394A568", 11),
  ("012394A5678", 11),
  ("12394A56708", 9),
  ("812394A5607", 11),
  ("12394A56087", 11),
  ("2394A560817", 9),
  ("72394A56018", 11),
  ("2394A560178", 11),
  ("394A5601728", 11),
  ("94A56017238", 11),
  ("4A560172398", 11),
  ("A5601723948", 9),
  ("8A560172349", 11),
  ("A5601723489", 11),
  ("560172348A9", 11),
  ("60172348A59", 11),
  ("0172348A569", 11),
  ("172348A5609", 11),
  ("72348A56019", 11),
  ("2348A560179", 11),
  ("348A5601729", 9),
  ("9348A560127", 11),
  ("348A5601297", 11),
  ("48A56012937", 11)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 12 := by decide

theorem based11 : basedOnCheck (List.range 11) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("4A586012739", 9)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("8A560129347", 11)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("8A560129347", 11),
  ("A5601293487", 11),
  ("560129348A7", 11),
  ("60129348A57", 9),
  ("7601293485A", 9),
  ("A7601293458", 11),
  ("760129345A8", 11),
  ("60129345A78", 11),
  ("0129345A768", 9),
  ("80129345A67", 11),
  ("0129345A687", 9),
  ("70129345A86", 9),
  ("6701293458A", 11),
  ("7012934586A", 11),
  ("0129345867A", 11),
  ("1293458670A", 9),
  ("A1293458607", 11),
  ("129345860A7", 9),
  ("712934586A0", 9),
  ("071293458A6", 9),
  ("607129345A8", 11),
  ("07129345A68", 11),
  ("7129345A608", 11),
  ("129345A6078", 11),
  ("29345A60718", 11),
  ("9345A607128", 11),
  ("345A6071298", 11),
  ("45A60712938", 9),
  ("845A6071239", 11),
  ("45A60712389", 11),
  ("5A607123849", 11),
  ("A6071238459", 11)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 20 := by decide

theorem based12 : basedOnCheck (List.range 11) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("8A560129347", 11)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("607123845A9", 11)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("607123845A9", 11),
  ("07123845A69", 11),
  ("7123845A609", 11),
  ("123845A6079", 11),
  ("23845A60719", 9),
  ("923845A6017", 11),
  ("23845A60197", 11),
  ("3845A601927", 11),
  ("845A6019237", 11),
  ("45A60192387", 11),
  ("5A601923847", 9),
  ("75A60192348", 11),
  ("5A601923478", 11),
  ("A6019234758", 9),
  ("8A601923457", 11),
  ("A6019234587", 11),
  ("601923458A7", 11),
  ("01923458A67", 9),
  ("7019234586A", 9),
  ("A7019234568", 11),
  ("701923456A8", 11),
  ("01923456A78", 11),
  ("1923456A708", 11),
  ("923456A7018", 11),
  ("23456A70198", 11),
  ("3456A701928", 9),
  ("83456A70129", 11),
  ("3456A701289", 11),
  ("456A7012839", 11),
  ("56A70128349", 11),
  ("6A701283459", 11),
  ("A7012834569", 11)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 12 := by decide

theorem based13 : basedOnCheck (List.range 11) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("607123845A9", 11)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("701283456A9", 11)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("701283456A9", 11),
  ("01283456A79", 11),
  ("1283456A709", 9),
  ("91283456A07", 11),
  ("1283456A097", 11),
  ("283456A0917", 11),
  ("83456A09127", 11),
  ("3456A091287", 11),
  ("456A0912837", 9),
  ("7456A091238", 11),
  ("456A0912378", 11),
  ("56A09123748", 9),
  ("856A0912347", 11),
  ("56A09123487", 11),
  ("6A091234857", 9),
  ("76A09123458", 11),
  ("6A091234578", 11),
  ("A0912345768", 11),
  ("091234576A8", 11),
  ("91234576A08", 11),
  ("1234576A098", 11),
  ("234576A0918", 9),
  ("8234576A019", 11),
  ("234576A0189", 11),
  ("34576A01829", 11),
  ("4576A018239", 11),
  ("576A0182349", 11),
  ("76A01823459", 11),
  ("6A018234579", 11),
  ("A0182345769", 9),
  ("9A018234567", 11),
  ("A0182345697", 11)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 12 := by decide

theorem based14 : basedOnCheck (List.range 11) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("701283456A9", 11)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("018234569A7", 11)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("018234569A7", 11),
  ("18234569A07", 11),
  ("8234569A017", 11),
  ("234569A0187", 11),
  ("34569A01827", 9),
  ("734569A0128", 11),
  ("34569A01278", 11),
  ("4569A012738", 9),
  ("84569A01237", 11),
  ("4569A012387", 11),
  ("569A0123847", 9),
  ("7569A012348", 11),
  ("569A0123478", 11),
  ("69A01234758", 11)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 14 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 6 := by decide

theorem based15 : basedOnCheck (List.range 11) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("018234569A7", 11)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("9A012347568", 11)) = true := by rfl

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

theorem rows_length : rows.length = 494 := by
  simp only [rows_blocks, List.length_append, length00, length01, length02, length03, length04, length05, length06, length07, length08, length09, length10, length11, length12, length13, length14, length15, Nat.reduceAdd]

theorem rows_charge : (rows.map Row.charge).sum = 222 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, charge08, charge09, charge10, charge11, charge12, charge13, charge14, charge15, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 11) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, based08, based09, based10, based11, based12, based13, based14, based15, Bool.and_self]

def suffix15 : List (Row Nat) := rows15

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("018234569A7", 11)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("701283456A9", 11)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("607123845A9", 11)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("8A560129347", 11)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("4A586012739", 9)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("7A456801239", 11)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("08123A45967", 11)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("90182A34567", 11)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("4560912A837", 9)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("8456019A237", 11)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("3485601A729", 9)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("7345860A129", 11)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("012349568A7", 11)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("6A081234597", 11)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("601823457A9", 11)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("345A6091287", 11)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("345A6091287", 11)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("9A012347568", 11)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.BlockF2Parts.C03
