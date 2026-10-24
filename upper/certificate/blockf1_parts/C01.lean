module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original BlockF1 rows 512 through 1023.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.BlockF1Parts.C01
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("901234A8567", 11),
  ("01234A85697", 11),
  ("1234A856907", 9),
  ("71234A85609", 11),
  ("1234A856079", 11),
  ("234A8560719", 11),
  ("34A85607129", 11),
  ("4A856071239", 11),
  ("A8560712349", 11),
  ("856071234A9", 11),
  ("56071234A89", 11),
  ("6071234A859", 9),
  ("96071234A58", 11),
  ("6071234A598", 11),
  ("071234A5968", 9),
  ("8071234A569", 11),
  ("071234A5689", 11),
  ("71234A56809", 11),
  ("1234A568079", 11),
  ("234A5680719", 9),
  ("9234A568017", 11),
  ("234A5680197", 11),
  ("34A56801927", 9),
  ("734A5680129", 11),
  ("34A56801279", 11),
  ("4A568012739", 11),
  ("A5680127349", 11),
  ("568012734A9", 11),
  ("68012734A59", 11),
  ("8012734A569", 11),
  ("012734A5689", 11),
  ("12734A56809", 9)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 12 := by decide

theorem based00 : basedOnCheck (List.range 11) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("901234A8567", 11)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("912734A5608", 11)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("912734A5608", 11),
  ("12734A56098", 11),
  ("2734A560918", 9),
  ("82734A56019", 11),
  ("2734A560189", 11),
  ("734A5601829", 11),
  ("34A56018279", 11),
  ("4A560182739", 9),
  ("94A56018237", 11),
  ("4A560182397", 11),
  ("A5601823947", 9),
  ("7A560182349", 11),
  ("A5601823479", 11),
  ("560182347A9", 11),
  ("60182347A59", 11),
  ("0182347A569", 11),
  ("182347A5609", 11),
  ("82347A56019", 11),
  ("2347A560189", 11),
  ("347A5601829", 9),
  ("9347A560128", 11),
  ("347A5601298", 11),
  ("47A56012938", 9),
  ("847A5601239", 11),
  ("47A56012389", 11),
  ("7A560123849", 11),
  ("A5601238479", 11),
  ("560123847A9", 11),
  ("60123847A59", 9),
  ("9601238475A", 9),
  ("A9601238457", 11),
  ("960123845A7", 11)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 14 := by decide

theorem based01 : basedOnCheck (List.range 11) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("912734A5608", 11)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("60123845A97", 11)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("60123845A97", 11),
  ("0123845A967", 9),
  ("70123845A69", 11),
  ("0123845A679", 11),
  ("123845A6709", 11),
  ("23845A67019", 11),
  ("3845A670129", 11),
  ("845A6701239", 11),
  ("45A67012389", 11),
  ("5A670123849", 9),
  ("95A67012348", 11),
  ("5A670123498", 11),
  ("A6701234958", 9),
  ("8A670123459", 11),
  ("A6701234589", 11),
  ("670123458A9", 11),
  ("70123458A69", 11),
  ("0123458A679", 11),
  ("123458A6709", 9),
  ("9123458A607", 11),
  ("123458A6097", 11),
  ("23458A60917", 9),
  ("723458A6019", 11),
  ("23458A60179", 11),
  ("3458A601729", 11),
  ("458A6017239", 11),
  ("58A60172349", 11),
  ("8A601723459", 11),
  ("A6017234589", 11),
  ("601723458A9", 11),
  ("01723458A69", 9),
  ("9017234586A", 9)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 14 := by decide

theorem based02 : basedOnCheck (List.range 11) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("60123845A97", 11)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("A9017234568", 11)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("A9017234568", 11),
  ("901723456A8", 11),
  ("01723456A98", 11),
  ("1723456A908", 9),
  ("81723456A09", 11),
  ("1723456A089", 11),
  ("723456A0819", 11),
  ("23456A08179", 11),
  ("3456A081729", 9),
  ("93456A08127", 11),
  ("3456A081297", 11),
  ("456A0812937", 9),
  ("7456A081239", 11),
  ("456A0812379", 11),
  ("56A08123749", 11),
  ("6A081237459", 11),
  ("A0812374569", 11),
  ("081237456A9", 11),
  ("81237456A09", 11),
  ("1237456A089", 11),
  ("237456A0819", 9),
  ("9237456A018", 11),
  ("237456A0198", 11),
  ("37456A01928", 9),
  ("837456A0129", 11),
  ("37456A01289", 11),
  ("7456A012839", 11),
  ("456A0128379", 11),
  ("56A01283749", 9),
  ("956A0128347", 11),
  ("56A01283497", 11),
  ("6A012834957", 9)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 14 := by decide

theorem based03 : basedOnCheck (List.range 11) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("A9017234568", 11)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("76A01283459", 11)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("76A01283459", 11),
  ("6A012834579", 11),
  ("A0128345769", 11),
  ("012834576A9", 11),
  ("12834576A09", 11),
  ("2834576A019", 11),
  ("834576A0129", 11),
  ("34576A01289", 11),
  ("4576A012839", 9),
  ("94576A01238", 11),
  ("4576A012398", 11),
  ("576A0123948", 9),
  ("8576A012349", 11),
  ("576A0123489", 11),
  ("76A01234859", 11),
  ("6A012348579", 11),
  ("A0123485769", 9),
  ("9A012348567", 11),
  ("A0123485697", 11),
  ("012348569A7", 11),
  ("12348569A07", 9),
  ("7123485690A", 9),
  ("A7123485609", 11),
  ("712348560A9", 11),
  ("12348560A79", 11),
  ("2348560A719", 11),
  ("348560A7129", 11),
  ("48560A71239", 11),
  ("8560A712349", 11),
  ("560A7123489", 11),
  ("60A71234859", 9),
  ("960A7123458", 11)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 12 := by decide

theorem based04 : basedOnCheck (List.range 11) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("76A01283459", 11)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("60A71234598", 11)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("60A71234598", 11),
  ("0A712345968", 9),
  ("80A71234569", 11),
  ("0A712345689", 11),
  ("A7123456809", 11),
  ("712345680A9", 11),
  ("12345680A79", 11),
  ("2345680A719", 9),
  ("92345680A17", 11),
  ("2345680A197", 11),
  ("345680A1927", 9),
  ("7345680A129", 11),
  ("345680A1279", 11),
  ("45680A12739", 11),
  ("5680A127349", 11),
  ("680A1273459", 11),
  ("80A12734569", 11),
  ("0A127345689", 11),
  ("A1273456809", 9),
  ("9A127345608", 11),
  ("A1273456098", 11),
  ("127345609A8", 11),
  ("27345609A18", 9),
  ("8273456091A", 9),
  ("A8273456019", 11),
  ("827345601A9", 11),
  ("27345601A89", 11),
  ("7345601A829", 11),
  ("345601A8279", 11),
  ("45601A82739", 9),
  ("945601A8237", 11),
  ("45601A82397", 11)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 14 := by decide

theorem based05 : basedOnCheck (List.range 11) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("60A71234598", 11)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("5601A823947", 9)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("5601A823947", 9),
  ("75601A82349", 11),
  ("5601A823479", 11),
  ("601A8234759", 11),
  ("01A82347569", 11),
  ("1A823475609", 11),
  ("A8234756019", 11),
  ("823475601A9", 11),
  ("23475601A89", 11),
  ("3475601A829", 9),
  ("93475601A28", 11),
  ("3475601A298", 11),
  ("475601A2938", 9),
  ("8475601A239", 11),
  ("475601A2389", 11),
  ("75601A23849", 11),
  ("5601A238479", 11),
  ("601A2384759", 9),
  ("9601A238457", 11),
  ("601A2384597", 11),
  ("01A23845967", 9),
  ("701A2384569", 11),
  ("01A23845679", 11),
  ("1A238456709", 11),
  ("A2384567019", 11),
  ("238456701A9", 11),
  ("38456701A29", 11),
  ("8456701A239", 11),
  ("456701A2389", 11),
  ("56701A23849", 9),
  ("956701A2348", 11),
  ("56701A23498", 11)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 12 := by decide

theorem based06 : basedOnCheck (List.range 11) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("5601A823947", 9)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("6701A234958", 9)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("6701A234958", 9),
  ("86701A23459", 11),
  ("6701A234589", 11),
  ("701A2345869", 11),
  ("01A23458679", 11),
  ("1A234586709", 9),
  ("91A23458607", 11),
  ("1A234586097", 11),
  ("A2345860917", 9),
  ("7A234586019", 11),
  ("A2345860179", 11),
  ("234586017A9", 11),
  ("34586017A29", 11),
  ("4586017A239", 11),
  ("586017A2349", 11),
  ("86017A23459", 11),
  ("6017A234589", 11),
  ("017A2345869", 9),
  ("9017A234568", 11),
  ("017A2345698", 11),
  ("17A23456908", 9),
  ("817A2345609", 11),
  ("17A23456089", 11),
  ("7A234560819", 11),
  ("A2345608179", 11),
  ("234560817A9", 11),
  ("34560817A29", 9),
  ("9345608172A", 9),
  ("A9345608127", 11),
  ("934560812A7", 11),
  ("34560812A97", 11),
  ("4560812A937", 9)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 16 := by decide

theorem based07 : basedOnCheck (List.range 11) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("6701A234958", 9)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("74560812A39", 11)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("74560812A39", 11),
  ("4560812A379", 11),
  ("560812A3749", 11),
  ("60812A37459", 11),
  ("0812A374569", 11),
  ("812A3745609", 11),
  ("12A37456089", 11),
  ("2A374560819", 9),
  ("92A37456018", 11),
  ("2A374560198", 11),
  ("A3745601928", 9),
  ("8A374560129", 11),
  ("A3745601289", 11),
  ("374560128A9", 11),
  ("74560128A39", 11),
  ("4560128A379", 11),
  ("560128A3749", 9),
  ("9560128A347", 11),
  ("560128A3497", 11),
  ("60128A34957", 9),
  ("760128A3459", 11),
  ("60128A34579", 11),
  ("0128A345769", 11),
  ("128A3457609", 11),
  ("28A34576019", 11),
  ("8A345760129", 11),
  ("A3457601289", 11),
  ("345760128A9", 11),
  ("45760128A39", 9),
  ("9457601283A", 9),
  ("A9457601238", 11),
  ("945760123A8", 11)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 12 := by decide

theorem based08 : basedOnCheck (List.range 11) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("74560812A39", 11)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("45760123A98", 11)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("45760123A98", 11),
  ("5760123A948", 9),
  ("85760123A49", 11),
  ("5760123A489", 11),
  ("760123A4859", 11),
  ("60123A48579", 11),
  ("0123A485769", 9),
  ("90123A48567", 11),
  ("0123A485697", 11),
  ("123A4856907", 9),
  ("7123A485609", 11),
  ("123A4856079", 11),
  ("23A48560719", 11),
  ("3A485607129", 11),
  ("A4856071239", 11),
  ("485607123A9", 11),
  ("85607123A49", 11),
  ("5607123A489", 11),
  ("607123A4859", 9),
  ("9607123A458", 11),
  ("607123A4598", 11),
  ("07123A45968", 9),
  ("807123A4569", 11),
  ("07123A45689", 11),
  ("7123A456809", 11),
  ("123A4568079", 11),
  ("23A45680719", 9),
  ("923A4568017", 11),
  ("23A45680197", 11),
  ("3A456801927", 9),
  ("73A45680129", 11),
  ("3A456801279", 11)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 14 := by decide

theorem based09 : basedOnCheck (List.range 11) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("45760123A98", 11)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("A4568012739", 11)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("A4568012739", 11),
  ("456801273A9", 11),
  ("56801273A49", 11),
  ("6801273A459", 11),
  ("801273A4569", 11),
  ("01273A45689", 11),
  ("1273A456809", 9),
  ("91273A45608", 11),
  ("1273A456098", 11),
  ("273A4560918", 9),
  ("8273A456019", 11),
  ("273A4560189", 11),
  ("73A45601829", 11),
  ("3A456018279", 11),
  ("A4560182739", 9),
  ("9A456018237", 11),
  ("A4560182397", 11),
  ("456018239A7", 11),
  ("56018239A47", 9),
  ("7560182394A", 9),
  ("A7560182349", 11),
  ("756018234A9", 11),
  ("56018234A79", 11),
  ("6018234A759", 11),
  ("018234A7569", 11),
  ("18234A75609", 11),
  ("8234A756019", 11),
  ("234A7560189", 11),
  ("34A75601829", 9),
  ("934A7560128", 11),
  ("34A75601298", 11),
  ("4A756012938", 9)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 14 := by decide

theorem based10 : basedOnCheck (List.range 11) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("A4568012739", 11)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("84A75601239", 11)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("84A75601239", 11),
  ("4A756012389", 11),
  ("A7560123849", 11),
  ("756012384A9", 11),
  ("56012384A79", 11),
  ("6012384A759", 9),
  ("96012384A57", 11),
  ("6012384A597", 11),
  ("012384A5967", 9),
  ("7012384A569", 11),
  ("012384A5679", 11),
  ("12384A56709", 11),
  ("2384A567019", 11),
  ("384A5670129", 11),
  ("84A56701239", 11),
  ("4A567012389", 11),
  ("A5670123849", 9),
  ("9A567012348", 11),
  ("A5670123498", 11),
  ("567012349A8", 11),
  ("67012349A58", 9),
  ("8670123495A", 9),
  ("A8670123459", 11),
  ("867012345A9", 11),
  ("67012345A89", 11),
  ("7012345A869", 11),
  ("012345A8679", 11),
  ("12345A86709", 9),
  ("912345A8607", 11),
  ("12345A86097", 11),
  ("2345A860917", 9),
  ("72345A86019", 11)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 14 := by decide

theorem based11 : basedOnCheck (List.range 11) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("84A75601239", 11)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("2345A860179", 11)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("2345A860179", 11),
  ("345A8601729", 11),
  ("45A86017239", 11),
  ("5A860172349", 11),
  ("A8601723459", 11),
  ("860172345A9", 11),
  ("60172345A89", 11),
  ("0172345A869", 9),
  ("90172345A68", 11),
  ("0172345A698", 11),
  ("172345A6908", 9),
  ("8172345A609", 11),
  ("172345A6089", 11),
  ("72345A60819", 11),
  ("2345A608179", 11),
  ("345A6081729", 9),
  ("9345A608127", 11),
  ("345A6081297", 11),
  ("45A60812937", 9),
  ("745A6081239", 11),
  ("45A60812379", 11),
  ("5A608123749", 11),
  ("A6081237459", 11),
  ("608123745A9", 11),
  ("08123745A69", 11),
  ("8123745A609", 11),
  ("123745A6089", 11),
  ("23745A60819", 9),
  ("923745A6018", 11),
  ("23745A60198", 11),
  ("3745A601928", 9),
  ("83745A60129", 11)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 12 := by decide

theorem based12 : basedOnCheck (List.range 11) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("2345A860179", 11)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("3745A601289", 11)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("3745A601289", 11),
  ("745A6012839", 11),
  ("45A60128379", 11),
  ("5A601283749", 9),
  ("95A60128347", 11),
  ("5A601283497", 11),
  ("A6012834957", 9),
  ("7A601283459", 11),
  ("A6012834579", 11),
  ("601283457A9", 11),
  ("01283457A69", 11),
  ("1283457A609", 11),
  ("283457A6019", 11),
  ("83457A60129", 11),
  ("3457A601289", 11),
  ("457A6012839", 9),
  ("9457A601238", 11),
  ("457A6012398", 11),
  ("57A60123948", 9),
  ("857A6012349", 11),
  ("57A60123489", 11),
  ("7A601234859", 11),
  ("A6012348579", 11),
  ("601234857A9", 11),
  ("01234857A69", 9),
  ("9012348576A", 9),
  ("A9012348567", 11),
  ("901234856A7", 11),
  ("01234856A97", 11),
  ("1234856A907", 9),
  ("71234856A09", 11),
  ("1234856A079", 11)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 14 := by decide

theorem based13 : basedOnCheck (List.range 11) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("3745A601289", 11)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("234856A0719", 11)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("234856A0719", 11),
  ("34856A07129", 11),
  ("4856A071239", 11),
  ("856A0712349", 11),
  ("56A07123489", 11),
  ("6A071234859", 9),
  ("96A07123458", 11),
  ("6A071234598", 11),
  ("A0712345968", 9),
  ("8A071234569", 11),
  ("A0712345689", 11),
  ("071234568A9", 11),
  ("71234568A09", 11),
  ("1234568A079", 11),
  ("234568A0719", 9),
  ("9234568A017", 11),
  ("234568A0197", 11),
  ("34568A01927", 9),
  ("734568A0129", 11),
  ("34568A01279", 11),
  ("4568A012739", 11),
  ("568A0127349", 11),
  ("68A01273459", 11),
  ("8A012734569", 11),
  ("A0127345689", 11),
  ("012734568A9", 11),
  ("12734568A09", 9),
  ("9127345680A", 9),
  ("A9127345608", 11),
  ("912734560A8", 11),
  ("12734560A98", 11),
  ("2734560A918", 9)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 14 := by decide

theorem based14 : basedOnCheck (List.range 11) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("234856A0719", 11)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("82734560A19", 11)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("82734560A19", 11),
  ("2734560A189", 11),
  ("734560A1829", 11),
  ("34560A18279", 11),
  ("4560A182739", 9),
  ("94560A18237", 11),
  ("4560A182397", 11),
  ("560A1823947", 9),
  ("7560A182349", 11),
  ("560A1823479", 11),
  ("60A18234759", 11),
  ("0A182347569", 11),
  ("A1823475609", 11),
  ("182347560A9", 11),
  ("82347560A19", 11),
  ("2347560A189", 11),
  ("347560A1829", 9),
  ("9347560A128", 11),
  ("347560A1298", 11),
  ("47560A12938", 9),
  ("847560A1239", 11),
  ("47560A12389", 11),
  ("7560A123849", 11),
  ("560A1238479", 11),
  ("60A12384759", 9),
  ("960A1238457", 11),
  ("60A12384597", 11),
  ("0A123845967", 9),
  ("70A12384569", 11),
  ("0A123845679", 11),
  ("A1238456709", 11),
  ("123845670A9", 11)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 32 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 12 := by decide

theorem based15 : basedOnCheck (List.range 11) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("82734560A19", 11)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("23845670A19", 11)) = true := by rfl

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

theorem rows_charge : (rows.map Row.charge).sum = 214 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, charge08, charge09, charge10, charge11, charge12, charge13, charge14, charge15, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 11) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, based08, based09, based10, based11, based12, based13, based14, based15, Bool.and_self]

def suffix15 : List (Row Nat) := rows15

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("82734560A19", 11)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("234856A0719", 11)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("3745A601289", 11)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("2345A860179", 11)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("84A75601239", 11)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("A4568012739", 11)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("45760123A98", 11)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("74560812A39", 11)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("6701A234958", 9)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("5601A823947", 9)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("60A71234598", 11)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("76A01283459", 11)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("A9017234568", 11)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("60123845A97", 11)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("912734A5608", 11)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("901234A8567", 11)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("23845670A19", 11)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("901234A8567", 11)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("23845670A19", 11)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.BlockF1Parts.C01
