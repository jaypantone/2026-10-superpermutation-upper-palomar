module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original BlockF2 rows 0 through 511.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.BlockF2Parts.C00
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("9A012347568", 11),
  ("A0123475698", 11),
  ("012347569A8", 11),
  ("12347569A08", 9),
  ("8123475690A", 9),
  ("A8123475609", 11),
  ("812347560A9", 11),
  ("12347560A89", 11),
  ("2347560A819", 11),
  ("347560A8129", 11),
  ("47560A81239", 11),
  ("7560A812349", 11),
  ("560A8123479", 11),
  ("60A81234759", 9),
  ("960A8123457", 11),
  ("60A81234597", 11),
  ("0A812345967", 11),
  ("A8123459607", 11),
  ("812345960A7", 11),
  ("12345960A87", 11),
  ("2345960A817", 9),
  ("72345960A18", 11),
  ("2345960A178", 9),
  ("82345960A71", 9),
  ("1823459607A", 11),
  ("8234596071A", 11),
  ("2345960718A", 11),
  ("3459607182A", 9),
  ("A3459607128", 11),
  ("345960712A8", 9),
  ("834596071A2", 9),
  ("283459607A1", 9)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 20 := by decide

theorem based00 : basedOnCheck (List.range 11) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("9A012347568", 11)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("128345960A7", 11)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("128345960A7", 11),
  ("28345960A17", 11),
  ("8345960A127", 11),
  ("345960A1287", 11),
  ("45960A12837", 9),
  ("745960A1238", 11),
  ("45960A12378", 11),
  ("5960A123748", 11),
  ("960A1237458", 11),
  ("60A12374598", 11),
  ("0A123745968", 9),
  ("80A12374569", 11),
  ("0A123745689", 11),
  ("A1237456809", 11),
  ("123745680A9", 11),
  ("23745680A19", 11),
  ("3745680A129", 11),
  ("745680A1239", 11),
  ("45680A12379", 11),
  ("5680A123749", 9),
  ("95680A12347", 11),
  ("5680A123497", 11),
  ("680A1234957", 11),
  ("80A12349567", 11),
  ("0A123495687", 11),
  ("A1234956807", 9),
  ("7A123495608", 11),
  ("A1234956078", 11),
  ("123495607A8", 11),
  ("23495607A18", 9),
  ("8234956071A", 9),
  ("A8234956017", 11)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 12 := by decide

theorem based01 : basedOnCheck (List.range 11) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("128345960A7", 11)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("823495601A7", 11)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("823495601A7", 11),
  ("23495601A87", 11),
  ("3495601A827", 9),
  ("73495601A28", 11),
  ("3495601A278", 11),
  ("495601A2738", 11),
  ("95601A27348", 11),
  ("5601A273498", 11),
  ("601A2734958", 9),
  ("8601A273459", 11),
  ("601A2734589", 11),
  ("01A27345869", 11),
  ("1A273458609", 11),
  ("A2734586019", 11),
  ("273458601A9", 11),
  ("73458601A29", 11),
  ("3458601A279", 11),
  ("458601A2739", 9),
  ("9458601A237", 11),
  ("458601A2397", 11),
  ("58601A23947", 11),
  ("8601A239457", 11),
  ("601A2394587", 11),
  ("01A23945867", 9),
  ("701A2394568", 11),
  ("01A23945678", 11),
  ("1A239456708", 11),
  ("A2394567018", 11),
  ("239456701A8", 9),
  ("823945670A1", 9),
  ("182394567A0", 9),
  ("018239456A7", 11)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 14 := by decide

theorem based02 : basedOnCheck (List.range 11) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("823495601A7", 11)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("18239456A07", 9)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("18239456A07", 9),
  ("7182394560A", 11),
  ("1823945607A", 11),
  ("8239456071A", 11),
  ("2394560718A", 9),
  ("A2394560781", 9),
  ("1A239456087", 11),
  ("A2394560817", 9),
  ("7A239456018", 11),
  ("A2394560178", 11),
  ("239456017A8", 11),
  ("39456017A28", 11),
  ("9456017A238", 11),
  ("456017A2398", 11),
  ("56017A23948", 9),
  ("856017A2349", 11),
  ("56017A23489", 11),
  ("6017A234859", 11),
  ("017A2348569", 11),
  ("17A23485609", 11),
  ("7A234856019", 11),
  ("A2348560179", 11),
  ("234856017A9", 11),
  ("34856017A29", 9),
  ("9348560172A", 9),
  ("A9348560127", 11),
  ("934856012A7", 11),
  ("34856012A97", 11),
  ("4856012A937", 11),
  ("856012A9347", 11),
  ("56012A93487", 11),
  ("6012A934857", 9)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 16 := by decide

theorem based03 : basedOnCheck (List.range 11) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("18239456A07", 9)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("76012A93458", 11)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("76012A93458", 11),
  ("6012A934578", 11),
  ("012A9345768", 9),
  ("8012A934567", 11),
  ("012A9345687", 11),
  ("12A93456807", 9),
  ("712A9345608", 11),
  ("12A93456078", 11),
  ("2A934560718", 11),
  ("A9345607128", 11),
  ("934560712A8", 11),
  ("34560712A98", 11),
  ("4560712A938", 9),
  ("84560712A39", 11),
  ("4560712A389", 11),
  ("560712A3849", 11),
  ("60712A38459", 11),
  ("0712A384569", 11),
  ("712A3845609", 11),
  ("12A38456079", 11),
  ("2A384560719", 9),
  ("92A38456017", 11),
  ("2A384560197", 11),
  ("A3845601927", 11),
  ("384560192A7", 11),
  ("84560192A37", 11),
  ("4560192A387", 11),
  ("560192A3847", 9),
  ("7560192A348", 11),
  ("560192A3478", 11),
  ("60192A34758", 9),
  ("860192A3457", 11)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 12 := by decide

theorem based04 : basedOnCheck (List.range 11) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("76012A93458", 11)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("60192A34587", 11)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("60192A34587", 11),
  ("0192A345867", 9),
  ("70192A34568", 11),
  ("0192A345678", 11),
  ("192A3456708", 11),
  ("92A34567018", 11),
  ("2A345670198", 11),
  ("A3456701928", 9),
  ("8A345670129", 11),
  ("A3456701289", 11),
  ("345670128A9", 11),
  ("45670128A39", 11),
  ("5670128A349", 11),
  ("670128A3459", 11),
  ("70128A34569", 11),
  ("0128A345679", 11),
  ("128A3456709", 9),
  ("9128A345607", 11),
  ("128A3456097", 11),
  ("28A34560917", 11),
  ("8A345609127", 11),
  ("A3456091287", 11),
  ("345609128A7", 11),
  ("45609128A37", 9),
  ("7456091283A", 9),
  ("A7456091238", 11),
  ("745609123A8", 11),
  ("45609123A78", 11),
  ("5609123A748", 9),
  ("85609123A47", 11),
  ("5609123A487", 9),
  ("75609123A84", 9)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 16 := by decide

theorem based05 : basedOnCheck (List.range 11) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("60192A34587", 11)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("4756091238A", 11)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("4756091238A", 11),
  ("7560912384A", 11),
  ("5609123847A", 11),
  ("6091238475A", 9),
  ("A6091238457", 11),
  ("609123845A7", 9),
  ("760912384A5", 9),
  ("576091238A4", 9),
  ("457609123A8", 11),
  ("57609123A48", 11),
  ("7609123A458", 11),
  ("609123A4578", 11),
  ("09123A45768", 11),
  ("9123A457608", 11),
  ("123A4576098", 11),
  ("23A45760918", 9),
  ("823A4576019", 11),
  ("23A45760189", 11),
  ("3A457601829", 11),
  ("A4576018239", 11),
  ("457601823A9", 11),
  ("57601823A49", 11),
  ("7601823A459", 11),
  ("601823A4579", 11),
  ("01823A45769", 9),
  ("901823A4567", 11),
  ("01823A45697", 11),
  ("1823A456907", 11),
  ("823A4569017", 11),
  ("23A45690187", 11),
  ("3A456901827", 9),
  ("73A45690128", 11)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 14 := by decide

theorem based06 : basedOnCheck (List.range 11) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("4756091238A", 11)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("3A456901278", 11)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("3A456901278", 11),
  ("A4569012738", 9),
  ("8A456901237", 11),
  ("A4569012387", 11),
  ("456901238A7", 11),
  ("56901238A47", 9),
  ("7569012384A", 9),
  ("A7569012348", 11),
  ("756901234A8", 11),
  ("56901234A78", 11),
  ("6901234A758", 11),
  ("901234A7568", 11),
  ("01234A75698", 11),
  ("1234A756908", 9),
  ("81234A75609", 11),
  ("1234A756089", 11),
  ("234A7560819", 11),
  ("34A75608129", 11),
  ("4A756081239", 11),
  ("A7560812349", 11),
  ("756081234A9", 11),
  ("56081234A79", 11),
  ("6081234A759", 9),
  ("96081234A57", 11),
  ("6081234A597", 11),
  ("081234A5967", 11),
  ("81234A59607", 11),
  ("1234A596087", 11),
  ("234A5960817", 9),
  ("7234A596018", 11),
  ("234A5960178", 11),
  ("34A59601728", 9)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 14 := by decide

theorem based07 : basedOnCheck (List.range 11) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("3A456901278", 11)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("834A5960127", 11)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("834A5960127", 11),
  ("34A59601287", 11),
  ("4A596012837", 9),
  ("74A59601238", 11),
  ("4A596012378", 11),
  ("A5960123748", 11),
  ("596012374A8", 11),
  ("96012374A58", 11),
  ("6012374A598", 11),
  ("012374A5968", 9),
  ("8012374A569", 11),
  ("012374A5689", 11),
  ("12374A56809", 11),
  ("2374A568019", 11),
  ("374A5680129", 11),
  ("74A56801239", 11),
  ("4A568012379", 11),
  ("A5680123749", 9),
  ("9A568012347", 11),
  ("A5680123497", 11),
  ("568012349A7", 11),
  ("68012349A57", 11),
  ("8012349A567", 11),
  ("012349A5687", 11),
  ("12349A56807", 9),
  ("712349A5608", 11),
  ("12349A56078", 11),
  ("2349A560718", 9),
  ("82349A56017", 11),
  ("2349A560187", 11),
  ("349A5601827", 9),
  ("7349A560128", 11)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 12 := by decide

theorem based08 : basedOnCheck (List.range 11) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("834A5960127", 11)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("349A5601278", 11)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("349A5601278", 11),
  ("49A56012738", 11),
  ("9A560127348", 11),
  ("A5601273498", 11),
  ("560127349A8", 11),
  ("60127349A58", 9),
  ("8601273495A", 9),
  ("A8601273459", 11),
  ("860127345A9", 11),
  ("60127345A89", 11),
  ("0127345A869", 11),
  ("127345A8609", 11),
  ("27345A86019", 11),
  ("7345A860129", 11),
  ("345A8601279", 11),
  ("45A86012739", 9),
  ("945A8601237", 11),
  ("45A86012397", 11),
  ("5A860123947", 11),
  ("A8601239457", 11),
  ("860123945A7", 11),
  ("60123945A87", 11),
  ("0123945A867", 9),
  ("70123945A68", 11),
  ("0123945A678", 9),
  ("80123945A76", 9),
  ("6801239457A", 11),
  ("8012394576A", 11),
  ("0123945768A", 11),
  ("1239457680A", 9),
  ("A1239457608", 11),
  ("123945760A8", 9)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 16 := by decide

theorem based09 : basedOnCheck (List.range 11) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("349A5601278", 11)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("812394576A0", 9)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("812394576A0", 9),
  ("081239457A6", 9),
  ("608123945A7", 11),
  ("08123945A67", 11),
  ("8123945A607", 11),
  ("123945A6087", 11),
  ("23945A60817", 9),
  ("723945A6018", 11),
  ("23945A60178", 11),
  ("3945A601728", 11),
  ("945A6017238", 11),
  ("45A60172398", 11),
  ("5A601723948", 9),
  ("85A60172349", 11),
  ("5A601723489", 11),
  ("A6017234859", 11),
  ("601723485A9", 11),
  ("01723485A69", 11),
  ("1723485A609", 11),
  ("723485A6019", 11),
  ("23485A60179", 11),
  ("3485A601729", 9),
  ("93485A60127", 11),
  ("3485A601297", 11),
  ("485A6012937", 11),
  ("85A60129347", 11),
  ("5A601293487", 11),
  ("A6012934857", 9),
  ("7A601293458", 11),
  ("A6012934578", 11),
  ("601293457A8", 11),
  ("01293457A68", 9)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 14 := by decide

theorem based10 : basedOnCheck (List.range 11) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("812394576A0", 9)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("8012934576A", 9)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("8012934576A", 9),
  ("A8012934567", 11),
  ("801293456A7", 11),
  ("01293456A87", 11),
  ("1293456A807", 9),
  ("71293456A08", 11),
  ("1293456A078", 11),
  ("293456A0718", 11),
  ("93456A07128", 11),
  ("3456A071298", 11),
  ("456A0712938", 9),
  ("8456A071239", 11),
  ("456A0712389", 11),
  ("56A07123849", 11),
  ("6A071238459", 11),
  ("A0712384569", 11),
  ("071238456A9", 11),
  ("71238456A09", 11),
  ("1238456A079", 11),
  ("238456A0719", 9),
  ("9238456A017", 11),
  ("238456A0197", 11),
  ("38456A01927", 11),
  ("8456A019237", 11),
  ("456A0192387", 11),
  ("56A01923847", 9),
  ("756A0192348", 11),
  ("56A01923478", 11),
  ("6A019234758", 11),
  ("A0192347568", 11),
  ("019234756A8", 9),
  ("801923475A6", 9)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 14 := by decide

theorem based11 : basedOnCheck (List.range 11) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("8012934576A", 9)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("680192347A5", 9)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("680192347A5", 9),
  ("568019234A7", 11),
  ("68019234A57", 9),
  ("7680192345A", 11),
  ("6801923457A", 11),
  ("8019234576A", 11),
  ("0192345768A", 9),
  ("A0192345786", 9),
  ("6A019234587", 11),
  ("A0192345867", 9),
  ("7A019234568", 11),
  ("A0192345678", 11),
  ("019234567A8", 11),
  ("19234567A08", 11),
  ("9234567A018", 11),
  ("234567A0198", 11),
  ("34567A01928", 9),
  ("834567A0129", 11),
  ("34567A01289", 11),
  ("4567A012839", 11),
  ("567A0128349", 11),
  ("67A01283459", 11),
  ("7A012834569", 11),
  ("A0128345679", 11),
  ("012834567A9", 11),
  ("12834567A09", 9),
  ("9128345670A", 9),
  ("A9128345607", 11),
  ("912834560A7", 11),
  ("12834560A97", 11),
  ("2834560A917", 11),
  ("834560A9127", 11)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 16 := by decide

theorem based12 : basedOnCheck (List.range 11) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("680192347A5", 9)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("34560A91287", 11)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("34560A91287", 11),
  ("4560A912837", 9),
  ("74560A91238", 11),
  ("4560A912378", 11),
  ("560A9123748", 9),
  ("8560A912347", 11),
  ("560A9123487", 11),
  ("60A91234857", 9),
  ("760A9123458", 11),
  ("60A91234578", 11),
  ("0A912345768", 11),
  ("A9123457608", 11),
  ("912345760A8", 11),
  ("12345760A98", 11),
  ("2345760A918", 9),
  ("82345760A19", 11),
  ("2345760A189", 11),
  ("345760A1829", 11),
  ("45760A18239", 11),
  ("5760A182349", 11),
  ("760A1823459", 11),
  ("60A18234579", 11),
  ("0A182345769", 9),
  ("90A18234567", 11),
  ("0A182345697", 11),
  ("A1823456907", 11),
  ("182345690A7", 11),
  ("82345690A17", 11),
  ("2345690A187", 11),
  ("345690A1827", 9),
  ("7345690A128", 11),
  ("345690A1278", 11)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 12 := by decide

theorem based13 : basedOnCheck (List.range 11) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("34560A91287", 11)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("45690A12738", 9)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("45690A12738", 9),
  ("845690A1237", 11),
  ("45690A12387", 11),
  ("5690A123847", 9),
  ("75690A12348", 11),
  ("5690A123478", 11),
  ("690A1234758", 11),
  ("90A12347568", 11),
  ("0A123475698", 11),
  ("A1234756908", 9),
  ("8A123475609", 11),
  ("A1234756089", 11),
  ("123475608A9", 11),
  ("23475608A19", 11),
  ("3475608A129", 11),
  ("475608A1239", 11),
  ("75608A12349", 11),
  ("5608A123479", 11),
  ("608A1234759", 9),
  ("9608A123457", 11),
  ("608A1234597", 11),
  ("08A12345967", 11),
  ("8A123459607", 11),
  ("A1234596087", 11),
  ("123459608A7", 11),
  ("23459608A17", 9),
  ("7234596081A", 9),
  ("A7234596018", 11),
  ("723459601A8", 11),
  ("23459601A78", 11),
  ("3459601A728", 9),
  ("83459601A27", 11)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 14 := by decide

theorem based14 : basedOnCheck (List.range 11) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("45690A12738", 9)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("3459601A287", 9)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("3459601A287", 9),
  ("73459601A82", 9),
  ("2734596018A", 11),
  ("7345960182A", 11),
  ("3459601827A", 11),
  ("4596018273A", 9),
  ("A4596018237", 11),
  ("459601823A7", 9),
  ("745960182A3", 9),
  ("374596018A2", 9),
  ("237459601A8", 11),
  ("37459601A28", 11),
  ("7459601A238", 11),
  ("459601A2378", 11),
  ("59601A23748", 11),
  ("9601A237458", 11),
  ("601A2374598", 11),
  ("01A23745968", 9),
  ("801A2374569", 11),
  ("01A23745689", 11),
  ("1A237456809", 11),
  ("A2374568019", 11),
  ("237456801A9", 11),
  ("37456801A29", 11),
  ("7456801A239", 11),
  ("456801A2379", 11),
  ("56801A23749", 9),
  ("956801A2347", 11),
  ("56801A23497", 11),
  ("6801A234957", 11),
  ("801A2349567", 11),
  ("01A23495687", 11)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 32 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 16 := by decide

theorem based15 : basedOnCheck (List.range 11) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("3459601A287", 9)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("1A234956807", 9)) = true := by rfl

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

theorem rows_charge : (rows.map Row.charge).sum = 232 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, charge08, charge09, charge10, charge11, charge12, charge13, charge14, charge15, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 11) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, based08, based09, based10, based11, based12, based13, based14, based15, Bool.and_self]

def suffix15 : List (Row Nat) := rows15

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("3459601A287", 9)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("45690A12738", 9)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("34560A91287", 11)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("680192347A5", 9)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("8012934576A", 9)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("812394576A0", 9)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("349A5601278", 11)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("834A5960127", 11)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("3A456901278", 11)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("4756091238A", 11)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("60192A34587", 11)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("76012A93458", 11)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("18239456A07", 9)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("823495601A7", 11)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("128345960A7", 11)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("9A012347568", 11)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("1A234956807", 9)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("9A012347568", 11)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("1A234956807", 9)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.BlockF2Parts.C00
