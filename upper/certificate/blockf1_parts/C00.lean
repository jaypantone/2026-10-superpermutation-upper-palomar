module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original BlockF1 rows 0 through 511.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.BlockF1Parts.C00
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("A0123458679", 11),
  ("012345867A9", 11),
  ("12345867A09", 9),
  ("9123458670A", 9),
  ("A9123458607", 11),
  ("912345860A7", 11),
  ("12345860A97", 11),
  ("2345860A917", 9),
  ("72345860A19", 11),
  ("2345860A179", 11),
  ("345860A1729", 11),
  ("45860A17239", 11),
  ("5860A172349", 11),
  ("860A1723459", 11),
  ("60A17234589", 11),
  ("0A172345869", 9),
  ("90A17234568", 11),
  ("0A172345698", 11),
  ("A1723456908", 9),
  ("8A172345609", 11),
  ("A1723456089", 11),
  ("172345608A9", 11),
  ("72345608A19", 11),
  ("2345608A179", 11),
  ("345608A1729", 9),
  ("9345608A127", 11),
  ("345608A1297", 11),
  ("45608A12937", 9),
  ("745608A1239", 11),
  ("45608A12379", 11),
  ("5608A123749", 11),
  ("608A1237459", 11)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 14 := by decide

theorem based00 : basedOnCheck (List.range 11) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("A0123458679", 11)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("08A12374569", 11)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("08A12374569", 11),
  ("8A123745609", 11),
  ("A1237456089", 11),
  ("123745608A9", 11),
  ("23745608A19", 9),
  ("9237456081A", 9),
  ("A9237456018", 11),
  ("923745601A8", 11),
  ("23745601A98", 11),
  ("3745601A928", 9),
  ("83745601A29", 11),
  ("3745601A289", 11),
  ("745601A2839", 11),
  ("45601A28379", 11),
  ("5601A283749", 9),
  ("95601A28347", 11),
  ("5601A283497", 11),
  ("601A2834957", 9),
  ("7601A283459", 11),
  ("601A2834579", 11),
  ("01A28345769", 11),
  ("1A283457609", 11),
  ("A2834576019", 11),
  ("283457601A9", 11),
  ("83457601A29", 11),
  ("3457601A289", 11),
  ("457601A2839", 9),
  ("9457601A238", 11),
  ("457601A2398", 11),
  ("57601A23948", 9),
  ("857601A2349", 11),
  ("57601A23489", 11)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 14 := by decide

theorem based01 : basedOnCheck (List.range 11) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("08A12374569", 11)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("7601A234859", 11)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("7601A234859", 11),
  ("601A2348579", 11),
  ("01A23485769", 9),
  ("901A2348567", 11),
  ("01A23485697", 11),
  ("1A234856907", 9),
  ("71A23485609", 11),
  ("1A234856079", 11),
  ("A2348560719", 11),
  ("234856071A9", 11),
  ("34856071A29", 11),
  ("4856071A239", 11),
  ("856071A2349", 11),
  ("56071A23489", 11),
  ("6071A234859", 9),
  ("96071A23458", 11),
  ("6071A234598", 11),
  ("071A2345968", 9),
  ("8071A234569", 11),
  ("071A2345689", 11),
  ("71A23456809", 11),
  ("1A234568079", 11),
  ("A2345680719", 9),
  ("9A234568017", 11),
  ("A2345680197", 11),
  ("234568019A7", 11),
  ("34568019A27", 9),
  ("7345680192A", 9),
  ("A7345680129", 11),
  ("734568012A9", 11),
  ("34568012A79", 11),
  ("4568012A739", 11)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 14 := by decide

theorem based02 : basedOnCheck (List.range 11) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("7601A234859", 11)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("568012A7349", 11)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("568012A7349", 11),
  ("68012A73459", 11),
  ("8012A734569", 11),
  ("012A7345689", 11),
  ("12A73456809", 9),
  ("912A7345608", 11),
  ("12A73456098", 11),
  ("2A734560918", 9),
  ("82A73456019", 11),
  ("2A734560189", 11),
  ("A7345601829", 11),
  ("734560182A9", 11),
  ("34560182A79", 11),
  ("4560182A739", 9),
  ("94560182A37", 11),
  ("4560182A397", 11),
  ("560182A3947", 9),
  ("7560182A349", 11),
  ("560182A3479", 11),
  ("60182A34759", 11),
  ("0182A347569", 11),
  ("182A3475609", 11),
  ("82A34756019", 11),
  ("2A347560189", 11),
  ("A3475601829", 9),
  ("9A347560128", 11),
  ("A3475601298", 11),
  ("347560129A8", 11),
  ("47560129A38", 9),
  ("8475601293A", 9),
  ("A8475601239", 11),
  ("847560123A9", 11)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 14 := by decide

theorem based03 : basedOnCheck (List.range 11) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("568012A7349", 11)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("47560123A89", 11)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("47560123A89", 11),
  ("7560123A849", 11),
  ("560123A8479", 11),
  ("60123A84759", 9),
  ("960123A8457", 11),
  ("60123A84597", 11),
  ("0123A845967", 9),
  ("70123A84569", 11),
  ("0123A845679", 11),
  ("123A8456709", 11),
  ("23A84567019", 11),
  ("3A845670129", 11),
  ("A8456701239", 11),
  ("845670123A9", 11),
  ("45670123A89", 11),
  ("5670123A849", 9),
  ("95670123A48", 11),
  ("5670123A498", 11),
  ("670123A4958", 9),
  ("8670123A459", 11),
  ("670123A4589", 11),
  ("70123A45869", 11),
  ("0123A458679", 11),
  ("123A4586709", 9),
  ("9123A458607", 11),
  ("123A4586097", 11),
  ("23A45860917", 9),
  ("723A4586019", 11),
  ("23A45860179", 11),
  ("3A458601729", 11),
  ("A4586017239", 11),
  ("458601723A9", 11)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 12 := by decide

theorem based04 : basedOnCheck (List.range 11) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("47560123A89", 11)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("58601723A49", 11)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("58601723A49", 11),
  ("8601723A459", 11),
  ("601723A4589", 11),
  ("01723A45869", 9),
  ("901723A4568", 11),
  ("01723A45698", 11),
  ("1723A456908", 9),
  ("81723A45609", 11),
  ("1723A456089", 11),
  ("723A4560819", 11),
  ("23A45608179", 11),
  ("3A456081729", 9),
  ("93A45608127", 11),
  ("3A456081297", 11),
  ("A4560812937", 9),
  ("7A456081239", 11),
  ("A4560812379", 11),
  ("456081237A9", 11),
  ("56081237A49", 11),
  ("6081237A459", 11),
  ("081237A4569", 11),
  ("81237A45609", 11),
  ("1237A456089", 11),
  ("237A4560819", 9),
  ("9237A456018", 11),
  ("237A4560198", 11),
  ("37A45601928", 9),
  ("837A4560129", 11),
  ("37A45601289", 11),
  ("7A456012839", 11),
  ("A4560128379", 11),
  ("456012837A9", 11)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 12 := by decide

theorem based05 : basedOnCheck (List.range 11) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("58601723A49", 11)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("56012837A49", 9)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("56012837A49", 9),
  ("9560128374A", 9),
  ("A9560128347", 11),
  ("956012834A7", 11),
  ("56012834A97", 11),
  ("6012834A957", 9),
  ("76012834A59", 11),
  ("6012834A579", 11),
  ("012834A5769", 11),
  ("12834A57609", 11),
  ("2834A576019", 11),
  ("834A5760129", 11),
  ("34A57601289", 11),
  ("4A576012839", 9),
  ("94A57601238", 11),
  ("4A576012398", 11),
  ("A5760123948", 9),
  ("8A576012349", 11),
  ("A5760123489", 11),
  ("576012348A9", 11),
  ("76012348A59", 11),
  ("6012348A579", 11),
  ("012348A5769", 9),
  ("9012348A567", 11),
  ("012348A5697", 11),
  ("12348A56907", 9),
  ("712348A5609", 11),
  ("12348A56079", 11),
  ("2348A560719", 11),
  ("348A5607129", 11),
  ("48A56071239", 11),
  ("8A560712349", 11)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 14 := by decide

theorem based06 : basedOnCheck (List.range 11) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("56012837A49", 9)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("A5607123489", 11)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("A5607123489", 11),
  ("560712348A9", 11),
  ("60712348A59", 9),
  ("9607123485A", 9),
  ("A9607123458", 11),
  ("960712345A8", 11),
  ("60712345A98", 11),
  ("0712345A968", 9),
  ("80712345A69", 11),
  ("0712345A689", 11),
  ("712345A6809", 11),
  ("12345A68079", 11),
  ("2345A680719", 9),
  ("92345A68017", 11),
  ("2345A680197", 11),
  ("345A6801927", 9),
  ("7345A680129", 11),
  ("345A6801279", 11),
  ("45A68012739", 11),
  ("5A680127349", 11),
  ("A6801273459", 11),
  ("680127345A9", 11),
  ("80127345A69", 11),
  ("0127345A689", 11),
  ("127345A6809", 9),
  ("9127345A608", 11),
  ("127345A6098", 11),
  ("27345A60918", 9),
  ("827345A6019", 11),
  ("27345A60189", 11),
  ("7345A601829", 11),
  ("345A6018279", 11)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 14 := by decide

theorem based07 : basedOnCheck (List.range 11) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("A5607123489", 11)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("45A60182739", 9)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("45A60182739", 9),
  ("945A6018237", 11),
  ("45A60182397", 11),
  ("5A601823947", 9),
  ("75A60182349", 11),
  ("5A601823479", 11),
  ("A6018234759", 11),
  ("601823475A9", 11),
  ("01823475A69", 11),
  ("1823475A609", 11),
  ("823475A6019", 11),
  ("23475A60189", 11),
  ("3475A601829", 9),
  ("93475A60128", 11),
  ("3475A601298", 11),
  ("475A6012938", 9),
  ("8475A601239", 11),
  ("475A6012389", 11),
  ("75A60123849", 11),
  ("5A601238479", 11),
  ("A6012384759", 9),
  ("9A601238457", 11),
  ("A6012384597", 11),
  ("601238459A7", 11),
  ("01238459A67", 9),
  ("7012384596A", 9),
  ("A7012384569", 11),
  ("701238456A9", 11),
  ("01238456A79", 11),
  ("1238456A709", 11),
  ("238456A7019", 11),
  ("38456A70129", 11)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 14 := by decide

theorem based08 : basedOnCheck (List.range 11) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("45A60182739", 9)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("8456A701239", 11)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("8456A701239", 11),
  ("456A7012389", 11),
  ("56A70123849", 9),
  ("956A7012348", 11),
  ("56A70123498", 11),
  ("6A701234958", 9),
  ("86A70123459", 11),
  ("6A701234589", 11),
  ("A7012345869", 11),
  ("701234586A9", 11),
  ("01234586A79", 11),
  ("1234586A709", 9),
  ("91234586A07", 11),
  ("1234586A097", 11),
  ("234586A0917", 9),
  ("7234586A019", 11),
  ("234586A0179", 11),
  ("34586A01729", 11),
  ("4586A017239", 11),
  ("586A0172349", 11),
  ("86A01723459", 11),
  ("6A017234589", 11),
  ("A0172345869", 9),
  ("9A017234568", 11),
  ("A0172345698", 11),
  ("017234569A8", 11),
  ("17234569A08", 9),
  ("8172345690A", 9),
  ("A8172345609", 11),
  ("817234560A9", 11),
  ("17234560A89", 11),
  ("7234560A819", 11)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 14 := by decide

theorem based09 : basedOnCheck (List.range 11) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("8456A701239", 11)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("234560A8179", 11)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("234560A8179", 11),
  ("34560A81729", 9),
  ("934560A8127", 11),
  ("34560A81297", 11),
  ("4560A812937", 9),
  ("74560A81239", 11),
  ("4560A812379", 11),
  ("560A8123749", 11),
  ("60A81237459", 11),
  ("0A812374569", 11),
  ("A8123745609", 11),
  ("812374560A9", 11),
  ("12374560A89", 11),
  ("2374560A819", 9),
  ("92374560A18", 11),
  ("2374560A198", 11),
  ("374560A1928", 9),
  ("8374560A129", 11),
  ("374560A1289", 11),
  ("74560A12839", 11),
  ("4560A128379", 11),
  ("560A1283749", 9),
  ("9560A128347", 11),
  ("560A1283497", 11),
  ("60A12834957", 9),
  ("760A1283459", 11),
  ("60A12834579", 11),
  ("0A128345769", 11),
  ("A1283457609", 11),
  ("128345760A9", 11),
  ("28345760A19", 11),
  ("8345760A129", 11)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 12 := by decide

theorem based10 : basedOnCheck (List.range 11) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("234560A8179", 11)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("345760A1289", 11)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("345760A1289", 11),
  ("45760A12839", 9),
  ("945760A1238", 11),
  ("45760A12398", 11),
  ("5760A123948", 9),
  ("85760A12349", 11),
  ("5760A123489", 11),
  ("760A1234859", 11),
  ("60A12348579", 11),
  ("0A123485769", 9),
  ("90A12348567", 11),
  ("0A123485697", 11),
  ("A1234856907", 9),
  ("7A123485609", 11),
  ("A1234856079", 11),
  ("123485607A9", 11),
  ("23485607A19", 11),
  ("3485607A129", 11),
  ("485607A1239", 11),
  ("85607A12349", 11),
  ("5607A123489", 11),
  ("607A1234859", 9),
  ("9607A123458", 11),
  ("607A1234598", 11),
  ("07A12345968", 9),
  ("807A1234569", 11),
  ("07A12345689", 11),
  ("7A123456809", 11),
  ("A1234568079", 11),
  ("123456807A9", 11),
  ("23456807A19", 9),
  ("9234568071A", 9)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 16 := by decide

theorem based11 : basedOnCheck (List.range 11) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("345760A1289", 11)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("A9234568017", 11)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("A9234568017", 11),
  ("923456801A7", 11),
  ("23456801A97", 11),
  ("3456801A927", 9),
  ("73456801A29", 11),
  ("3456801A279", 11),
  ("456801A2739", 11),
  ("56801A27349", 11),
  ("6801A273459", 11),
  ("801A2734569", 11),
  ("01A27345689", 11),
  ("1A273456809", 9),
  ("91A27345608", 11),
  ("1A273456098", 11),
  ("A2734560918", 9),
  ("8A273456019", 11),
  ("A2734560189", 11),
  ("273456018A9", 11),
  ("73456018A29", 11),
  ("3456018A279", 11),
  ("456018A2739", 9),
  ("9456018A237", 11),
  ("456018A2397", 11),
  ("56018A23947", 9),
  ("756018A2349", 11),
  ("56018A23479", 11),
  ("6018A234759", 11),
  ("018A2347569", 11),
  ("18A23475609", 11),
  ("8A234756019", 11),
  ("A2347560189", 11),
  ("234756018A9", 11)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 10 := by decide

theorem based12 : basedOnCheck (List.range 11) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("A9234568017", 11)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("34756018A29", 9)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("34756018A29", 9),
  ("9347560182A", 9),
  ("A9347560128", 11),
  ("934756012A8", 11),
  ("34756012A98", 11),
  ("4756012A938", 9),
  ("84756012A39", 11),
  ("4756012A389", 11),
  ("756012A3849", 11),
  ("56012A38479", 11),
  ("6012A384759", 9),
  ("96012A38457", 11),
  ("6012A384597", 11),
  ("012A3845967", 9),
  ("7012A384569", 11),
  ("012A3845679", 11),
  ("12A38456709", 11),
  ("2A384567019", 11),
  ("A3845670129", 11),
  ("384567012A9", 11),
  ("84567012A39", 11),
  ("4567012A389", 11),
  ("567012A3849", 9),
  ("9567012A348", 11),
  ("567012A3498", 11),
  ("67012A34958", 9),
  ("867012A3459", 11),
  ("67012A34589", 11),
  ("7012A345869", 11),
  ("012A3458679", 11),
  ("12A34586709", 9),
  ("912A3458607", 11)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 16 := by decide

theorem based13 : basedOnCheck (List.range 11) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("34756018A29", 9)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("12A34586097", 11)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("12A34586097", 11),
  ("2A345860917", 9),
  ("72A34586019", 11),
  ("2A345860179", 11),
  ("A3458601729", 11),
  ("345860172A9", 11),
  ("45860172A39", 11),
  ("5860172A349", 11),
  ("860172A3459", 11),
  ("60172A34589", 11),
  ("0172A345869", 9),
  ("90172A34568", 11),
  ("0172A345698", 11),
  ("172A3456908", 9),
  ("8172A345609", 11),
  ("172A3456089", 11),
  ("72A34560819", 11),
  ("2A345608179", 11),
  ("A3456081729", 9),
  ("9A345608127", 11),
  ("A3456081297", 11),
  ("345608129A7", 11),
  ("45608129A37", 9),
  ("7456081293A", 9),
  ("A7456081239", 11),
  ("745608123A9", 11),
  ("45608123A79", 11),
  ("5608123A749", 11),
  ("608123A7459", 11),
  ("08123A74569", 11),
  ("8123A745609", 11),
  ("123A7456089", 11)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 12 := by decide

theorem based14 : basedOnCheck (List.range 11) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("12A34586097", 11)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("23A74560819", 9)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("23A74560819", 9),
  ("923A7456018", 11),
  ("23A74560198", 11),
  ("3A745601928", 9),
  ("83A74560129", 11),
  ("3A745601289", 11),
  ("A7456012839", 11),
  ("745601283A9", 11),
  ("45601283A79", 11),
  ("5601283A749", 9),
  ("95601283A47", 11),
  ("5601283A497", 11),
  ("601283A4957", 9),
  ("7601283A459", 11),
  ("601283A4579", 11),
  ("01283A45769", 11),
  ("1283A457609", 11),
  ("283A4576019", 11),
  ("83A45760129", 11),
  ("3A457601289", 11),
  ("A4576012839", 9),
  ("9A457601238", 11),
  ("A4576012398", 11),
  ("457601239A8", 11),
  ("57601239A48", 9),
  ("8576012394A", 9),
  ("A8576012349", 11),
  ("857601234A9", 11),
  ("57601234A89", 11),
  ("7601234A859", 11),
  ("601234A8579", 11),
  ("01234A85769", 9)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 32 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 16 := by decide

theorem based15 : basedOnCheck (List.range 11) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("23A74560819", 9)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("901234A8567", 11)) = true := by rfl

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

theorem rows_charge : (rows.map Row.charge).sum = 218 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, charge08, charge09, charge10, charge11, charge12, charge13, charge14, charge15, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 11) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, based08, based09, based10, based11, based12, based13, based14, based15, Bool.and_self]

def suffix15 : List (Row Nat) := rows15

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("23A74560819", 9)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("12A34586097", 11)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("34756018A29", 9)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("A9234568017", 11)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("345760A1289", 11)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("234560A8179", 11)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("8456A701239", 11)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("45A60182739", 9)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("A5607123489", 11)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("56012837A49", 9)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("58601723A49", 11)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("47560123A89", 11)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("568012A7349", 11)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("7601A234859", 11)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("08A12374569", 11)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("A0123458679", 11)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("901234A8567", 11)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("A0123458679", 11)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("901234A8567", 11)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.BlockF1Parts.C00
