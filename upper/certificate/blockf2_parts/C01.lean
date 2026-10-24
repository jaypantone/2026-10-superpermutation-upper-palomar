module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original BlockF2 rows 512 through 1023.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.BlockF2Parts.C01
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("1A234956807", 9),
  ("71A23495608", 11),
  ("1A234956078", 11),
  ("A2349560718", 9),
  ("8A234956017", 11),
  ("A2349560187", 11),
  ("234956018A7", 11),
  ("34956018A27", 9),
  ("7349560182A", 9),
  ("A7349560128", 11),
  ("734956012A8", 11),
  ("34956012A78", 11),
  ("4956012A738", 11),
  ("956012A7348", 11),
  ("56012A73498", 11),
  ("6012A734958", 9),
  ("86012A73459", 11),
  ("6012A734589", 11),
  ("012A7345869", 11),
  ("12A73458609", 11),
  ("2A734586019", 11),
  ("A7345860129", 11),
  ("734586012A9", 11),
  ("34586012A79", 11),
  ("4586012A739", 9),
  ("94586012A37", 11),
  ("4586012A397", 11),
  ("586012A3947", 11),
  ("86012A39457", 11),
  ("6012A394587", 11),
  ("012A3945867", 9),
  ("7012A394568", 11)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 14 := by decide

theorem based00 : basedOnCheck (List.range 11) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("1A234956807", 9)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("012A3945678", 11)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("012A3945678", 11),
  ("12A39456708", 9),
  ("812A3945607", 11),
  ("12A39456087", 11),
  ("2A394560817", 9),
  ("72A39456018", 11),
  ("2A394560178", 11),
  ("A3945601728", 11),
  ("394560172A8", 11),
  ("94560172A38", 11),
  ("4560172A398", 11),
  ("560172A3948", 9),
  ("8560172A349", 11),
  ("560172A3489", 11),
  ("60172A34859", 11),
  ("0172A348569", 11),
  ("172A3485609", 11),
  ("72A34856019", 11),
  ("2A348560179", 11),
  ("A3485601729", 9),
  ("9A348560127", 11),
  ("A3485601297", 11),
  ("348560129A7", 11),
  ("48560129A37", 11),
  ("8560129A347", 11),
  ("560129A3487", 11),
  ("60129A34857", 9),
  ("760129A3458", 11),
  ("60129A34578", 11),
  ("0129A345768", 9),
  ("80129A34567", 11),
  ("0129A345687", 11)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 12 := by decide

theorem based01 : basedOnCheck (List.range 11) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("012A3945678", 11)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("129A3456807", 9)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("129A3456807", 9),
  ("7129A345608", 11),
  ("129A3456078", 11),
  ("29A34560718", 11),
  ("9A345607128", 11),
  ("A3456071298", 11),
  ("345607129A8", 11),
  ("45607129A38", 9),
  ("8456071293A", 9),
  ("A8456071239", 11),
  ("845607123A9", 11),
  ("45607123A89", 11),
  ("5607123A849", 11),
  ("607123A8459", 11),
  ("07123A84569", 11),
  ("7123A845609", 11),
  ("123A8456079", 11),
  ("23A84560719", 9),
  ("923A8456017", 11),
  ("23A84560197", 11),
  ("3A845601927", 11),
  ("A8456019237", 11),
  ("845601923A7", 11),
  ("45601923A87", 11),
  ("5601923A847", 9),
  ("75601923A48", 11),
  ("5601923A478", 9),
  ("85601923A74", 9),
  ("4856019237A", 11),
  ("8560192374A", 11),
  ("5601923748A", 11),
  ("6019237485A", 9)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 16 := by decide

theorem based02 : basedOnCheck (List.range 11) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("129A3456807", 9)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("A6019237458", 11)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("A6019237458", 11),
  ("601923745A8", 9),
  ("860192374A5", 9),
  ("586019237A4", 9),
  ("458601923A7", 11),
  ("58601923A47", 11),
  ("8601923A457", 11),
  ("601923A4587", 11),
  ("01923A45867", 9),
  ("701923A4568", 11),
  ("01923A45678", 11),
  ("1923A456708", 11),
  ("923A4567018", 11),
  ("23A45670198", 11),
  ("3A456701928", 9),
  ("83A45670129", 11),
  ("3A456701289", 11),
  ("A4567012839", 11),
  ("456701283A9", 11),
  ("56701283A49", 11),
  ("6701283A459", 11),
  ("701283A4569", 11),
  ("01283A45679", 11),
  ("1283A456709", 9),
  ("91283A45607", 11),
  ("1283A456097", 11),
  ("283A4560917", 11),
  ("83A45609127", 11),
  ("3A456091287", 11),
  ("A4560912837", 9),
  ("7A456091238", 11),
  ("A4560912378", 11)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 14 := by decide

theorem based03 : basedOnCheck (List.range 11) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("A6019237458", 11)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("456091237A8", 11)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("456091237A8", 11),
  ("56091237A48", 9),
  ("8560912374A", 9),
  ("A8560912347", 11),
  ("856091234A7", 11),
  ("56091234A87", 11),
  ("6091234A857", 9),
  ("76091234A58", 11),
  ("6091234A578", 11),
  ("091234A5768", 11),
  ("91234A57608", 11),
  ("1234A576098", 11),
  ("234A5760918", 9),
  ("8234A576019", 11),
  ("234A5760189", 11),
  ("34A57601829", 11),
  ("4A576018239", 11),
  ("A5760182349", 11),
  ("576018234A9", 11),
  ("76018234A59", 11),
  ("6018234A579", 11),
  ("018234A5769", 9),
  ("9018234A567", 11),
  ("018234A5697", 11),
  ("18234A56907", 11),
  ("8234A569017", 11),
  ("234A5690187", 11),
  ("34A56901827", 9),
  ("734A5690128", 11),
  ("34A56901278", 11),
  ("4A569012738", 11),
  ("A5690127348", 11)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 12 := by decide

theorem based04 : basedOnCheck (List.range 11) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("456091237A8", 11)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("569012734A8", 9)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("569012734A8", 9),
  ("856901273A4", 9),
  ("485690127A3", 9),
  ("348569012A7", 11),
  ("48569012A37", 9),
  ("7485690123A", 11),
  ("4856901237A", 11),
  ("8569012374A", 11),
  ("5690123748A", 9),
  ("A5690123784", 9),
  ("4A569012387", 11),
  ("A5690123847", 9),
  ("7A569012348", 11),
  ("A5690123478", 11),
  ("569012347A8", 11),
  ("69012347A58", 11),
  ("9012347A568", 11),
  ("012347A5698", 11),
  ("12347A56908", 9),
  ("812347A5609", 11),
  ("12347A56089", 11),
  ("2347A560819", 11),
  ("347A5608129", 11),
  ("47A56081239", 11),
  ("7A560812349", 11),
  ("A5608123479", 11),
  ("560812347A9", 11),
  ("60812347A59", 9),
  ("9608123475A", 9),
  ("A9608123457", 11),
  ("960812345A7", 11),
  ("60812345A97", 11)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 20 := by decide

theorem based05 : basedOnCheck (List.range 11) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("569012734A8", 9)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("0812345A967", 11)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("0812345A967", 11),
  ("812345A9607", 11),
  ("12345A96087", 11),
  ("2345A960817", 9),
  ("72345A96018", 11),
  ("2345A960178", 11),
  ("345A9601728", 9),
  ("8345A960127", 11),
  ("345A9601287", 11),
  ("45A96012837", 9),
  ("745A9601238", 11),
  ("45A96012378", 11),
  ("5A960123748", 11),
  ("A9601237458", 11),
  ("960123745A8", 11),
  ("60123745A98", 11),
  ("0123745A968", 9),
  ("80123745A69", 11),
  ("0123745A689", 11),
  ("123745A6809", 11),
  ("23745A68019", 11),
  ("3745A680129", 11),
  ("745A6801239", 11),
  ("45A68012379", 11),
  ("5A680123749", 9),
  ("95A68012347", 11),
  ("5A680123497", 11),
  ("A6801234957", 11),
  ("680123495A7", 11),
  ("80123495A67", 11),
  ("0123495A687", 11),
  ("123495A6807", 9)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 12 := by decide

theorem based06 : basedOnCheck (List.range 11) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("0812345A967", 11)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("7123495A608", 11)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("7123495A608", 11),
  ("123495A6078", 11),
  ("23495A60718", 9),
  ("823495A6017", 11),
  ("23495A60187", 11),
  ("3495A601827", 9),
  ("73495A60128", 11),
  ("3495A601278", 11),
  ("495A6012738", 11),
  ("95A60127348", 11),
  ("5A601273498", 11),
  ("A6012734958", 9),
  ("8A601273459", 11),
  ("A6012734589", 11),
  ("601273458A9", 11),
  ("01273458A69", 11),
  ("1273458A609", 11),
  ("273458A6019", 11),
  ("73458A60129", 11),
  ("3458A601279", 11),
  ("458A6012739", 9),
  ("9458A601237", 11),
  ("458A6012397", 11),
  ("58A60123947", 11),
  ("8A601239457", 11),
  ("A6012394587", 11),
  ("601239458A7", 11),
  ("01239458A67", 9),
  ("7012394586A", 9),
  ("A7012394568", 11),
  ("701239456A8", 11),
  ("01239456A78", 11)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 12 := by decide

theorem based07 : basedOnCheck (List.range 11) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("7123495A608", 11)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("1239456A708", 9)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("1239456A708", 9),
  ("81239456A07", 11),
  ("1239456A087", 9),
  ("71239456A80", 9),
  ("0712394568A", 11),
  ("7123945680A", 11),
  ("1239456807A", 11),
  ("2394568071A", 9),
  ("A2394568017", 11),
  ("239456801A7", 9),
  ("723945680A1", 9),
  ("172394568A0", 9),
  ("017239456A8", 11),
  ("17239456A08", 11),
  ("7239456A018", 11),
  ("239456A0178", 11),
  ("39456A01728", 11),
  ("9456A017238", 11),
  ("456A0172398", 11),
  ("56A01723948", 9),
  ("856A0172349", 11),
  ("56A01723489", 11),
  ("6A017234859", 11),
  ("A0172348569", 11),
  ("017234856A9", 11),
  ("17234856A09", 11),
  ("7234856A019", 11),
  ("234856A0179", 11),
  ("34856A01729", 9),
  ("934856A0127", 11),
  ("34856A01297", 11),
  ("4856A012937", 11)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 18 := by decide

theorem based08 : basedOnCheck (List.range 11) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("1239456A708", 9)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("856A0129347", 11)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("856A0129347", 11),
  ("56A01293487", 11),
  ("6A012934857", 9),
  ("76A01293458", 11),
  ("6A012934578", 11),
  ("A0129345768", 9),
  ("8A012934567", 11),
  ("A0129345687", 11),
  ("012934568A7", 11),
  ("12934568A07", 9),
  ("7129345680A", 9),
  ("A7129345608", 11),
  ("712934560A8", 11),
  ("12934560A78", 11),
  ("2934560A718", 11),
  ("934560A7128", 11),
  ("34560A71298", 11),
  ("4560A712938", 9),
  ("84560A71239", 11),
  ("4560A712389", 11),
  ("560A7123849", 11),
  ("60A71238459", 11),
  ("0A712384569", 11),
  ("A7123845609", 11),
  ("712384560A9", 11),
  ("12384560A79", 11),
  ("2384560A719", 9),
  ("92384560A17", 11),
  ("2384560A197", 11),
  ("384560A1927", 11),
  ("84560A19237", 11),
  ("4560A192387", 11)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 12 := by decide

theorem based09 : basedOnCheck (List.range 11) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("856A0129347", 11)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("560A1923847", 9)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("560A1923847", 9),
  ("7560A192348", 11),
  ("560A1923478", 11),
  ("60A19234758", 9),
  ("860A1923457", 11),
  ("60A19234587", 11),
  ("0A192345867", 9),
  ("70A19234568", 11),
  ("0A192345678", 11),
  ("A1923456708", 11),
  ("192345670A8", 11),
  ("92345670A18", 11),
  ("2345670A198", 11),
  ("345670A1928", 9),
  ("8345670A129", 11),
  ("345670A1289", 11),
  ("45670A12839", 11),
  ("5670A128349", 11),
  ("670A1283459", 11),
  ("70A12834569", 11),
  ("0A128345679", 11),
  ("A1283456709", 9),
  ("9A128345607", 11),
  ("A1283456097", 11),
  ("128345609A7", 11),
  ("28345609A17", 11),
  ("8345609A127", 11),
  ("345609A1287", 11),
  ("45609A12837", 9),
  ("745609A1238", 11),
  ("45609A12378", 11),
  ("5609A123748", 9)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 14 := by decide

theorem based10 : basedOnCheck (List.range 11) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("560A1923847", 9)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("85609A12347", 11)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("85609A12347", 11),
  ("5609A123487", 11),
  ("609A1234857", 9),
  ("7609A123458", 11),
  ("609A1234578", 11),
  ("09A12345768", 11),
  ("9A123457608", 11),
  ("A1234576098", 11),
  ("123457609A8", 11),
  ("23457609A18", 9),
  ("8234576091A", 9),
  ("A8234576019", 11),
  ("823457601A9", 11),
  ("23457601A89", 11),
  ("3457601A829", 11),
  ("457601A8239", 11),
  ("57601A82349", 11),
  ("7601A823459", 11),
  ("601A8234579", 11),
  ("01A82345769", 9),
  ("901A8234567", 11),
  ("01A82345697", 11),
  ("1A823456907", 11),
  ("A8234569017", 11),
  ("823456901A7", 11),
  ("23456901A87", 11),
  ("3456901A827", 9),
  ("73456901A28", 11),
  ("3456901A278", 9),
  ("83456901A72", 9),
  ("2834569017A", 11),
  ("8345690172A", 11)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 14 := by decide

theorem based11 : basedOnCheck (List.range 11) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("85609A12347", 11)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("3456901728A", 11)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("3456901728A", 11),
  ("4569017283A", 9),
  ("A4569017238", 11),
  ("456901723A8", 9),
  ("845690172A3", 9),
  ("384569017A2", 9),
  ("238456901A7", 11),
  ("38456901A27", 11),
  ("8456901A237", 11),
  ("456901A2387", 11),
  ("56901A23847", 9),
  ("756901A2348", 11),
  ("56901A23478", 11),
  ("6901A234758", 11),
  ("901A2347568", 11),
  ("01A23475698", 11),
  ("1A234756908", 9),
  ("81A23475609", 11),
  ("1A234756089", 11),
  ("A2347560819", 11),
  ("234756081A9", 11),
  ("34756081A29", 11),
  ("4756081A239", 11),
  ("756081A2349", 11),
  ("56081A23479", 11),
  ("6081A234759", 9),
  ("96081A23457", 11),
  ("6081A234597", 11),
  ("081A2345967", 11),
  ("81A23459607", 11),
  ("1A234596087", 11),
  ("A2345960817", 9)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 16 := by decide

theorem based12 : basedOnCheck (List.range 11) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("3456901728A", 11)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("7A234596018", 11)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("7A234596018", 11),
  ("A2345960178", 11),
  ("234596017A8", 11),
  ("34596017A28", 9),
  ("8345960172A", 9),
  ("A8345960127", 11),
  ("834596012A7", 11),
  ("34596012A87", 11),
  ("4596012A837", 9),
  ("74596012A38", 11),
  ("4596012A378", 11),
  ("596012A3748", 11),
  ("96012A37458", 11),
  ("6012A374598", 11),
  ("012A3745968", 9),
  ("8012A374569", 11),
  ("012A3745689", 11),
  ("12A37456809", 11),
  ("2A374568019", 11),
  ("A3745680129", 11),
  ("374568012A9", 11),
  ("74568012A39", 11),
  ("4568012A379", 11),
  ("568012A3749", 9),
  ("9568012A347", 11),
  ("568012A3497", 11),
  ("68012A34957", 11),
  ("8012A349567", 11),
  ("012A3495687", 11),
  ("12A34956807", 9),
  ("712A3495608", 11),
  ("12A34956078", 11)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 12 := by decide

theorem based13 : basedOnCheck (List.range 11) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("7A234596018", 11)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("2A349560718", 11)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("2A349560718", 11),
  ("A3495607128", 11),
  ("349560712A8", 9),
  ("834956071A2", 9),
  ("283495607A1", 9),
  ("128349560A7", 11),
  ("28349560A17", 9),
  ("7283495601A", 11),
  ("2834956017A", 11),
  ("8349560172A", 11),
  ("3495601728A", 9),
  ("A3495601782", 9),
  ("2A349560187", 11),
  ("A3495601827", 9),
  ("7A349560128", 11),
  ("A3495601278", 11),
  ("349560127A8", 11),
  ("49560127A38", 11),
  ("9560127A348", 11),
  ("560127A3498", 11),
  ("60127A34958", 9),
  ("860127A3459", 11),
  ("60127A34589", 11),
  ("0127A345869", 11),
  ("127A3458609", 11),
  ("27A34586019", 11),
  ("7A345860129", 11),
  ("A3458601279", 11),
  ("345860127A9", 11),
  ("45860127A39", 9),
  ("9458601273A", 9),
  ("A9458601237", 11)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 20 := by decide

theorem based14 : basedOnCheck (List.range 11) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("2A349560718", 11)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("945860123A7", 11)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("945860123A7", 11),
  ("45860123A97", 11),
  ("5860123A947", 11),
  ("860123A9457", 11),
  ("60123A94587", 11),
  ("0123A945867", 9),
  ("70123A94568", 11),
  ("0123A945678", 11),
  ("123A9456708", 9),
  ("8123A945607", 11),
  ("123A9456087", 11),
  ("23A94560817", 9),
  ("723A9456018", 11),
  ("23A94560178", 11),
  ("3A945601728", 11),
  ("A9456017238", 11),
  ("945601723A8", 11),
  ("45601723A98", 11),
  ("5601723A948", 9),
  ("85601723A49", 11),
  ("5601723A489", 11),
  ("601723A4859", 11),
  ("01723A48569", 11),
  ("1723A485609", 11),
  ("723A4856019", 11),
  ("23A48560179", 11),
  ("3A485601729", 9),
  ("93A48560127", 11),
  ("3A485601297", 11),
  ("A4856012937", 11),
  ("485601293A7", 11),
  ("85601293A47", 11)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 32 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 10 := by decide

theorem based15 : basedOnCheck (List.range 11) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("945860123A7", 11)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("5601293A487", 11)) = true := by rfl

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

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("945860123A7", 11)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("2A349560718", 11)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("7A234596018", 11)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("3456901728A", 11)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("85609A12347", 11)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("560A1923847", 9)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("856A0129347", 11)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("1239456A708", 9)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("7123495A608", 11)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("0812345A967", 11)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("569012734A8", 9)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("456091237A8", 11)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("A6019237458", 11)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("129A3456807", 9)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("012A3945678", 11)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("1A234956807", 9)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("5601293A487", 11)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("1A234956807", 9)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("5601293A487", 11)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.BlockF2Parts.C01
