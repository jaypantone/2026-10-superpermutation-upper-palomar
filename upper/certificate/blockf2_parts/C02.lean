module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original BlockF2 rows 1024 through 1535.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.BlockF2Parts.C02
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("5601293A487", 11),
  ("601293A4857", 9),
  ("7601293A458", 11),
  ("601293A4578", 11),
  ("01293A45768", 9),
  ("801293A4567", 11),
  ("01293A45687", 11),
  ("1293A456807", 9),
  ("71293A45608", 11),
  ("1293A456078", 11),
  ("293A4560718", 11),
  ("93A45607128", 11),
  ("3A456071298", 11),
  ("A4560712938", 9),
  ("8A456071239", 11),
  ("A4560712389", 11),
  ("456071238A9", 11),
  ("56071238A49", 11),
  ("6071238A459", 11),
  ("071238A4569", 11),
  ("71238A45609", 11),
  ("1238A456079", 11),
  ("238A4560719", 9),
  ("9238A456017", 11),
  ("238A4560197", 11),
  ("38A45601927", 11),
  ("8A456019237", 11),
  ("A4560192387", 11),
  ("456019238A7", 11),
  ("56019238A47", 9),
  ("7560192384A", 9),
  ("A7560192348", 11)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 14 := by decide

theorem based00 : basedOnCheck (List.range 11) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("5601293A487", 11)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("756019234A8", 11)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("756019234A8", 11),
  ("56019234A78", 11),
  ("6019234A758", 9),
  ("86019234A57", 11),
  ("6019234A587", 9),
  ("76019234A85", 9),
  ("5760192348A", 11),
  ("7601923485A", 11),
  ("6019234857A", 11),
  ("0192348576A", 9),
  ("A0192348567", 11),
  ("019234856A7", 9),
  ("701923485A6", 9),
  ("670192348A5", 9),
  ("567019234A8", 11),
  ("67019234A58", 11),
  ("7019234A568", 11),
  ("019234A5678", 11),
  ("19234A56708", 11),
  ("9234A567018", 11),
  ("234A5670198", 11),
  ("34A56701928", 9),
  ("834A5670129", 11),
  ("34A56701289", 11),
  ("4A567012839", 11),
  ("A5670128349", 11),
  ("567012834A9", 11),
  ("67012834A59", 11),
  ("7012834A569", 11),
  ("012834A5679", 11),
  ("12834A56709", 9),
  ("912834A5607", 11)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 18 := by decide

theorem based01 : basedOnCheck (List.range 11) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("756019234A8", 11)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("12834A56097", 11)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("12834A56097", 11),
  ("2834A560917", 11),
  ("834A5609127", 11),
  ("34A56091287", 11),
  ("4A560912837", 9),
  ("74A56091238", 11),
  ("4A560912378", 11),
  ("A5609123748", 9),
  ("8A560912347", 11),
  ("A5609123487", 11),
  ("560912348A7", 11),
  ("60912348A57", 9),
  ("7609123485A", 9),
  ("A7609123458", 11),
  ("760912345A8", 11),
  ("60912345A78", 11),
  ("0912345A768", 11),
  ("912345A7608", 11),
  ("12345A76098", 11),
  ("2345A760918", 9),
  ("82345A76019", 11),
  ("2345A760189", 11),
  ("345A7601829", 11),
  ("45A76018239", 11),
  ("5A760182349", 11),
  ("A7601823459", 11),
  ("760182345A9", 11),
  ("60182345A79", 11),
  ("0182345A769", 9),
  ("90182345A67", 11),
  ("0182345A697", 11),
  ("182345A6907", 11)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 12 := by decide

theorem based02 : basedOnCheck (List.range 11) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("12834A56097", 11)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("82345A69017", 11)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("82345A69017", 11),
  ("2345A690187", 11),
  ("345A6901827", 9),
  ("7345A690128", 11),
  ("345A6901278", 11),
  ("45A69012738", 9),
  ("845A6901237", 11),
  ("45A69012387", 11),
  ("5A690123847", 9),
  ("75A69012348", 11),
  ("5A690123478", 11),
  ("A6901234758", 11),
  ("690123475A8", 11),
  ("90123475A68", 11),
  ("0123475A698", 11),
  ("123475A6908", 9),
  ("8123475A609", 11),
  ("123475A6089", 11),
  ("23475A60819", 11),
  ("3475A608129", 11),
  ("475A6081239", 11),
  ("75A60812349", 11),
  ("5A608123479", 11),
  ("A6081234759", 9),
  ("9A608123457", 11),
  ("A6081234597", 11),
  ("608123459A7", 11),
  ("08123459A67", 11),
  ("8123459A607", 11),
  ("123459A6087", 11),
  ("23459A60817", 9),
  ("723459A6018", 11)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 12 := by decide

theorem based03 : basedOnCheck (List.range 11) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("82345A69017", 11)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("23459A60178", 11)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("23459A60178", 11),
  ("3459A601728", 9),
  ("83459A60127", 11),
  ("3459A601287", 11),
  ("459A6012837", 9),
  ("7459A601238", 11),
  ("459A6012378", 11),
  ("59A60123748", 11),
  ("9A601237458", 11),
  ("A6012374598", 11),
  ("601237459A8", 11),
  ("01237459A68", 9),
  ("8012374596A", 9),
  ("A8012374569", 11),
  ("801237456A9", 11),
  ("01237456A89", 11),
  ("1237456A809", 11),
  ("237456A8019", 11),
  ("37456A80129", 11),
  ("7456A801239", 11),
  ("456A8012379", 11),
  ("56A80123749", 9),
  ("956A8012347", 11),
  ("56A80123497", 11),
  ("6A801234957", 11),
  ("A8012349567", 11),
  ("801234956A7", 11),
  ("01234956A87", 11),
  ("1234956A807", 9),
  ("71234956A08", 11),
  ("1234956A078", 9),
  ("81234956A70", 9)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 16 := by decide

theorem based04 : basedOnCheck (List.range 11) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("23459A60178", 11)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("0812349567A", 11)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("0812349567A", 11),
  ("8123495670A", 11),
  ("1234956708A", 11),
  ("2349567081A", 9),
  ("A2349567018", 11),
  ("234956701A8", 9),
  ("823495670A1", 9),
  ("182349567A0", 9),
  ("018234956A7", 11),
  ("18234956A07", 11),
  ("8234956A017", 11),
  ("234956A0187", 11),
  ("34956A01827", 9),
  ("734956A0128", 11),
  ("34956A01278", 11),
  ("4956A012738", 11),
  ("956A0127348", 11),
  ("56A01273498", 11),
  ("6A012734958", 9),
  ("86A01273459", 11),
  ("6A012734589", 11),
  ("A0127345869", 11),
  ("012734586A9", 11),
  ("12734586A09", 11),
  ("2734586A019", 11),
  ("734586A0129", 11),
  ("34586A01279", 11),
  ("4586A012739", 9),
  ("94586A01237", 11),
  ("4586A012397", 11),
  ("586A0123947", 11),
  ("86A01239457", 11)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 14 := by decide

theorem based05 : basedOnCheck (List.range 11) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("0812349567A", 11)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("6A012394587", 11)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("6A012394587", 11),
  ("A0123945867", 9),
  ("7A012394568", 11),
  ("A0123945678", 11),
  ("012394567A8", 11),
  ("12394567A08", 9),
  ("8123945670A", 9),
  ("A8123945607", 11),
  ("812394560A7", 11),
  ("12394560A87", 11),
  ("2394560A817", 9),
  ("72394560A18", 11),
  ("2394560A178", 11),
  ("394560A1728", 11),
  ("94560A17238", 11),
  ("4560A172398", 11),
  ("560A1723948", 9),
  ("8560A172349", 11),
  ("560A1723489", 11),
  ("60A17234859", 11),
  ("0A172348569", 11),
  ("A1723485609", 11),
  ("172348560A9", 11),
  ("72348560A19", 11),
  ("2348560A179", 11),
  ("348560A1729", 9),
  ("9348560A127", 11),
  ("348560A1297", 11),
  ("48560A12937", 11),
  ("8560A129347", 11),
  ("560A1293487", 11),
  ("60A12934857", 9)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 14 := by decide

theorem based06 : basedOnCheck (List.range 11) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("6A012394587", 11)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("760A1293458", 11)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("760A1293458", 11),
  ("60A12934578", 11),
  ("0A129345768", 11),
  ("A1293457608", 11),
  ("129345760A8", 9),
  ("812934576A0", 9),
  ("081293457A6", 9),
  ("608129345A7", 11),
  ("08129345A67", 9),
  ("7081293456A", 11),
  ("0812934567A", 11),
  ("8129345670A", 11),
  ("1293456708A", 9),
  ("A1293456780", 9),
  ("0A129345687", 11),
  ("A1293456807", 9),
  ("7A129345608", 11),
  ("A1293456078", 11),
  ("129345607A8", 11),
  ("29345607A18", 11),
  ("9345607A128", 11),
  ("345607A1298", 11),
  ("45607A12938", 9),
  ("845607A1239", 11),
  ("45607A12389", 11),
  ("5607A123849", 11),
  ("607A1238459", 11),
  ("07A12384569", 11),
  ("7A123845609", 11),
  ("A1238456079", 11),
  ("123845607A9", 11),
  ("23845607A19", 9)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 18 := by decide

theorem based07 : basedOnCheck (List.range 11) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("760A1293458", 11)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("9238456071A", 9)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("9238456071A", 9),
  ("A9238456017", 11),
  ("923845601A7", 11),
  ("23845601A97", 11),
  ("3845601A927", 11),
  ("845601A9237", 11),
  ("45601A92387", 11),
  ("5601A923847", 9),
  ("75601A92348", 11),
  ("5601A923478", 11),
  ("601A9234758", 9),
  ("8601A923457", 11),
  ("601A9234587", 11),
  ("01A92345867", 9),
  ("701A9234568", 11),
  ("01A92345678", 11),
  ("1A923456708", 11),
  ("A9234567018", 11),
  ("923456701A8", 11),
  ("23456701A98", 11),
  ("3456701A928", 9),
  ("83456701A29", 11),
  ("3456701A289", 11),
  ("456701A2839", 11),
  ("56701A28349", 11),
  ("6701A283459", 11),
  ("701A2834569", 11),
  ("01A28345679", 11),
  ("1A283456709", 9),
  ("91A28345607", 11),
  ("1A283456097", 11),
  ("A2834560917", 11)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 12 := by decide

theorem based08 : basedOnCheck (List.range 11) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("9238456071A", 9)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("283456091A7", 11)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("283456091A7", 11),
  ("83456091A27", 11),
  ("3456091A287", 11),
  ("456091A2837", 9),
  ("7456091A238", 11),
  ("456091A2378", 11),
  ("56091A23748", 9),
  ("856091A2347", 11),
  ("56091A23487", 11),
  ("6091A234857", 9),
  ("76091A23458", 11),
  ("6091A234578", 11),
  ("091A2345768", 11),
  ("91A23457608", 11),
  ("1A234576098", 11),
  ("A2345760918", 9),
  ("8A234576019", 11),
  ("A2345760189", 11),
  ("234576018A9", 11),
  ("34576018A29", 11),
  ("4576018A239", 11),
  ("576018A2349", 11),
  ("76018A23459", 11),
  ("6018A234579", 11),
  ("018A2345769", 9),
  ("9018A234567", 11),
  ("018A2345697", 11),
  ("18A23456907", 11),
  ("8A234569017", 11),
  ("A2345690187", 11),
  ("234569018A7", 11),
  ("34569018A27", 9)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 12 := by decide

theorem based09 : basedOnCheck (List.range 11) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("283456091A7", 11)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("7345690182A", 9)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("7345690182A", 9),
  ("A7345690128", 11),
  ("734569012A8", 11),
  ("34569012A78", 11),
  ("4569012A738", 9),
  ("84569012A37", 11),
  ("4569012A387", 9),
  ("74569012A83", 9),
  ("3745690128A", 11),
  ("7456901283A", 11),
  ("4569012837A", 11),
  ("5690128374A", 9),
  ("A5690128347", 11),
  ("569012834A7", 9),
  ("756901283A4", 9),
  ("475690128A3", 9),
  ("347569012A8", 11),
  ("47569012A38", 11),
  ("7569012A348", 11),
  ("569012A3478", 11),
  ("69012A34758", 11),
  ("9012A347568", 11),
  ("012A3475698", 11),
  ("12A34756908", 9),
  ("812A3475609", 11),
  ("12A34756089", 11),
  ("2A347560819", 11),
  ("A3475608129", 11),
  ("347560812A9", 11),
  ("47560812A39", 11),
  ("7560812A349", 11),
  ("560812A3479", 11)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 18 := by decide

theorem based10 : basedOnCheck (List.range 11) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("7345690182A", 9)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("60812A34759", 9)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("60812A34759", 9),
  ("960812A3457", 11),
  ("60812A34597", 11),
  ("0812A345967", 11),
  ("812A3459607", 11),
  ("12A34596087", 11),
  ("2A345960817", 9),
  ("72A34596018", 11),
  ("2A345960178", 11),
  ("A3459601728", 9),
  ("8A345960127", 11),
  ("A3459601287", 11),
  ("345960128A7", 11),
  ("45960128A37", 9),
  ("7459601283A", 9),
  ("A7459601238", 11),
  ("745960123A8", 11),
  ("45960123A78", 11),
  ("5960123A748", 11),
  ("960123A7458", 11),
  ("60123A74598", 11),
  ("0123A745968", 9),
  ("80123A74569", 11),
  ("0123A745689", 11),
  ("123A7456809", 11),
  ("23A74568019", 11),
  ("3A745680129", 11),
  ("A7456801239", 11),
  ("745680123A9", 11),
  ("45680123A79", 11),
  ("5680123A749", 9),
  ("95680123A47", 11)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 14 := by decide

theorem based11 : basedOnCheck (List.range 11) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("60812A34759", 9)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("5680123A497", 11)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("5680123A497", 11),
  ("680123A4957", 11),
  ("80123A49567", 11),
  ("0123A495687", 11),
  ("123A4956807", 9),
  ("7123A495608", 11),
  ("123A4956078", 11),
  ("23A49560718", 9),
  ("823A4956017", 11),
  ("23A49560187", 11),
  ("3A495601827", 9),
  ("73A49560128", 11),
  ("3A495601278", 11),
  ("A4956012738", 11),
  ("495601273A8", 11),
  ("95601273A48", 11),
  ("5601273A498", 11),
  ("601273A4958", 9),
  ("8601273A459", 11),
  ("601273A4589", 11),
  ("01273A45869", 11),
  ("1273A458609", 11),
  ("273A4586019", 11),
  ("73A45860129", 11),
  ("3A458601279", 11),
  ("A4586012739", 9),
  ("9A458601237", 11),
  ("A4586012397", 11),
  ("458601239A7", 11),
  ("58601239A47", 11),
  ("8601239A457", 11),
  ("601239A4587", 11)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 10 := by decide

theorem based12 : basedOnCheck (List.range 11) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("5680123A497", 11)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("01239A45867", 9)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("01239A45867", 9),
  ("701239A4568", 11),
  ("01239A45678", 11),
  ("1239A456708", 9),
  ("81239A45607", 11),
  ("1239A456087", 11),
  ("239A4560817", 9),
  ("7239A456018", 11),
  ("239A4560178", 11),
  ("39A45601728", 11),
  ("9A456017238", 11),
  ("A4560172398", 11),
  ("456017239A8", 11),
  ("56017239A48", 9),
  ("8560172394A", 9),
  ("A8560172349", 11),
  ("856017234A9", 11),
  ("56017234A89", 11),
  ("6017234A859", 11),
  ("017234A8569", 11),
  ("17234A85609", 11),
  ("7234A856019", 11),
  ("234A8560179", 11),
  ("34A85601729", 9),
  ("934A8560127", 11),
  ("34A85601297", 11),
  ("4A856012937", 11),
  ("A8560129347", 11),
  ("856012934A7", 11),
  ("56012934A87", 11),
  ("6012934A857", 9),
  ("76012934A58", 11)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 14 := by decide

theorem based13 : basedOnCheck (List.range 11) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("01239A45867", 9)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("6012934A578", 9)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("6012934A578", 9),
  ("86012934A75", 9),
  ("5860129347A", 11),
  ("8601293475A", 11),
  ("6012934758A", 11),
  ("0129347586A", 9),
  ("A0129347568", 11),
  ("012934756A8", 9),
  ("801293475A6", 9),
  ("680129347A5", 9),
  ("568012934A7", 11),
  ("68012934A57", 11),
  ("8012934A567", 11),
  ("012934A5687", 11),
  ("12934A56807", 9),
  ("712934A5608", 11),
  ("12934A56078", 11),
  ("2934A560718", 11),
  ("934A5607128", 11),
  ("34A56071298", 11),
  ("4A560712938", 9),
  ("84A56071239", 11),
  ("4A560712389", 11),
  ("A5607123849", 11),
  ("560712384A9", 11),
  ("60712384A59", 11),
  ("0712384A569", 11),
  ("712384A5609", 11),
  ("12384A56079", 11),
  ("2384A560719", 9),
  ("92384A56017", 11),
  ("2384A560197", 11)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 18 := by decide

theorem based14 : basedOnCheck (List.range 11) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("6012934A578", 9)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("384A5601927", 11)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("384A5601927", 11),
  ("84A56019237", 11),
  ("4A560192387", 11),
  ("A5601923847", 9),
  ("7A560192348", 11),
  ("A5601923478", 11),
  ("560192347A8", 11),
  ("60192347A58", 9),
  ("8601923475A", 9),
  ("A8601923457", 11),
  ("860192345A7", 11),
  ("60192345A87", 11),
  ("0192345A867", 9),
  ("70192345A68", 11),
  ("0192345A678", 11),
  ("192345A6708", 11),
  ("92345A67018", 11),
  ("2345A670198", 11),
  ("345A6701928", 9),
  ("8345A670129", 11),
  ("345A6701289", 11),
  ("45A67012839", 11),
  ("5A670128349", 11),
  ("A6701283459", 11),
  ("670128345A9", 11),
  ("70128345A69", 11),
  ("0128345A679", 11),
  ("128345A6709", 9),
  ("9128345A607", 11),
  ("128345A6097", 11),
  ("28345A60917", 11),
  ("8345A609127", 11)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 32 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 12 := by decide

theorem based15 : basedOnCheck (List.range 11) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("384A5601927", 11)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("345A6091287", 11)) = true := by rfl

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

theorem rows_charge : (rows.map Row.charge).sum = 228 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, charge08, charge09, charge10, charge11, charge12, charge13, charge14, charge15, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 11) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, based08, based09, based10, based11, based12, based13, based14, based15, Bool.and_self]

def suffix15 : List (Row Nat) := rows15

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("384A5601927", 11)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("6012934A578", 9)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("01239A45867", 9)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("5680123A497", 11)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("60812A34759", 9)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("7345690182A", 9)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("283456091A7", 11)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("9238456071A", 9)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("760A1293458", 11)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("6A012394587", 11)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("0812349567A", 11)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("23459A60178", 11)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("82345A69017", 11)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("12834A56097", 11)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("756019234A8", 11)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("5601293A487", 11)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("345A6091287", 11)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("5601293A487", 11)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("345A6091287", 11)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.BlockF2Parts.C02
