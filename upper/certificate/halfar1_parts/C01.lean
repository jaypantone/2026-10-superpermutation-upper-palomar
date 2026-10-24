module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original Halfar1 rows 512 through 1023.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.Halfar1Parts.C01
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("62473105", 8),
  ("24731065", 8),
  ("47310625", 6),
  ("54731026", 8),
  ("47310256", 8),
  ("73102546", 6),
  ("67310245", 8),
  ("73102465", 8),
  ("31024675", 8),
  ("10246735", 8),
  ("02467315", 8),
  ("24673105", 6),
  ("52467301", 8),
  ("24673051", 8),
  ("46730521", 8),
  ("67305241", 6),
  ("16730542", 8),
  ("67305412", 8),
  ("73054162", 8),
  ("30541672", 8),
  ("05416732", 6),
  ("20541637", 6),
  ("72054136", 8),
  ("20541376", 8),
  ("05413726", 8),
  ("54137206", 8),
  ("41372056", 6),
  ("64137250", 8),
  ("41372560", 8),
  ("13725640", 8),
  ("37256410", 6),
  ("03725614", 8)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 16 := by decide

theorem based00 : basedOnCheck (List.range 8) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("62473105", 8)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("37256104", 8)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("37256104", 8),
  ("72561034", 6),
  ("47256130", 8),
  ("72561340", 8),
  ("25613470", 8),
  ("56134720", 8),
  ("61347250", 6),
  ("06134752", 8),
  ("61347502", 8),
  ("13475062", 8),
  ("34750612", 8),
  ("47506132", 6),
  ("24750631", 8),
  ("47506321", 8),
  ("75063241", 8),
  ("50632471", 8),
  ("06324751", 6),
  ("10632457", 6),
  ("71063254", 8),
  ("10632574", 8),
  ("06325714", 8),
  ("63257104", 8),
  ("32571064", 6),
  ("43257160", 8),
  ("32571640", 8),
  ("25716430", 8),
  ("57164320", 6),
  ("05716423", 8),
  ("57164203", 8),
  ("71642053", 8),
  ("16420573", 8),
  ("64205713", 6)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 16 := by decide

theorem based01 : basedOnCheck (List.range 8) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("37256104", 8)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("36420517", 6)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("36420517", 6),
  ("73642015", 8),
  ("36420175", 8),
  ("64201735", 8),
  ("42017365", 8),
  ("20173645", 6),
  ("52017346", 8),
  ("20173456", 8),
  ("01734526", 6),
  ("60173425", 8),
  ("01734265", 8),
  ("17342605", 8),
  ("73426015", 6),
  ("57342610", 8),
  ("73426150", 8),
  ("34261570", 8),
  ("42615730", 8),
  ("26157340", 6),
  ("02615743", 8),
  ("26157403", 8),
  ("61574023", 8),
  ("15740263", 8),
  ("57402613", 6),
  ("35740216", 8),
  ("57402136", 8),
  ("74021356", 6),
  ("67402153", 8),
  ("74021563", 8),
  ("40215673", 8),
  ("02156743", 8),
  ("21567403", 6),
  ("32156704", 8)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 16 := by decide

theorem based02 : basedOnCheck (List.range 8) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("36420517", 6)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("21567034", 8)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("21567034", 8),
  ("15670324", 8),
  ("56703214", 6),
  ("45670312", 8),
  ("56703142", 8),
  ("67031452", 8),
  ("70314562", 8),
  ("03145672", 8),
  ("31456702", 6),
  ("23145607", 6),
  ("72314506", 8),
  ("23145076", 8),
  ("31450726", 8),
  ("14507236", 6),
  ("61450732", 8),
  ("14507362", 8),
  ("45073612", 8),
  ("50736142", 6),
  ("25073641", 8),
  ("50736421", 8),
  ("07364251", 8),
  ("73642501", 8),
  ("36425071", 8),
  ("64250731", 6),
  ("16425037", 6),
  ("71642530", 8),
  ("16425370", 8),
  ("64253710", 8),
  ("42537160", 8),
  ("25371640", 6),
  ("02537146", 8),
  ("25371406", 8)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 16 := by decide

theorem based03 : basedOnCheck (List.range 8) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("21567034", 8)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("53714026", 8)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("53714026", 8),
  ("37140256", 6),
  ("63714052", 8),
  ("37140562", 8),
  ("71405632", 8),
  ("14056372", 8),
  ("40563712", 6),
  ("24056317", 6),
  ("72405613", 8),
  ("24056173", 8),
  ("40561723", 8),
  ("05617243", 8),
  ("56172403", 6),
  ("35617204", 8),
  ("56172034", 8),
  ("61720354", 8),
  ("17203564", 6),
  ("41720365", 8),
  ("17203645", 8),
  ("72036415", 6),
  ("57203614", 8),
  ("72036154", 8),
  ("20361574", 8),
  ("03615724", 8),
  ("36157204", 6),
  ("43615702", 8),
  ("36157042", 8),
  ("61570432", 8),
  ("15704362", 6),
  ("21570463", 8),
  ("15704623", 8),
  ("57046213", 8)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 16 := by decide

theorem based04 : basedOnCheck (List.range 8) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("53714026", 8)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("70462153", 8)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("70462153", 8),
  ("04621573", 8),
  ("46215703", 6),
  ("34621507", 6),
  ("73462105", 8),
  ("34621075", 8),
  ("46210735", 8),
  ("62107345", 6),
  ("56210743", 8),
  ("62107453", 8),
  ("21074563", 8),
  ("10745623", 6),
  ("31074526", 8),
  ("10745236", 8),
  ("07452316", 8),
  ("74523106", 8),
  ("45231076", 8),
  ("52310746", 6),
  ("65231047", 6),
  ("76523140", 8),
  ("65231470", 8),
  ("52314760", 8),
  ("23147650", 8),
  ("31476520", 6),
  ("03147625", 8),
  ("31476205", 8),
  ("14762035", 8),
  ("47620315", 6),
  ("54762013", 8),
  ("47620153", 8),
  ("76201543", 8),
  ("62015473", 8)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 16 := by decide

theorem based05 : basedOnCheck (List.range 8) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("70462153", 8)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("20154763", 6)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("20154763", 6),
  ("32015467", 6),
  ("73201564", 8),
  ("32015674", 8),
  ("20156734", 8),
  ("01567324", 6),
  ("40156723", 8),
  ("01567243", 8),
  ("15672403", 8),
  ("56724013", 8),
  ("67240153", 6),
  ("36724051", 8),
  ("67240531", 8),
  ("72405361", 8),
  ("24053671", 8),
  ("40536721", 6),
  ("14053627", 6),
  ("71405326", 8),
  ("14053276", 8),
  ("40532716", 8),
  ("05327146", 8),
  ("53271406", 6),
  ("65327104", 8),
  ("53271064", 8),
  ("32710654", 8),
  ("27106534", 6),
  ("42710635", 8),
  ("27106345", 8),
  ("71063425", 8),
  ("10634275", 8),
  ("06342715", 6),
  ("50634217", 6)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 20 := by decide

theorem based06 : basedOnCheck (List.range 8) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("20154763", 6)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("75063412", 8)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("75063412", 8),
  ("50634172", 8),
  ("06341752", 8),
  ("63417502", 6),
  ("26341705", 8),
  ("63417025", 8),
  ("34170265", 8),
  ("41702635", 6),
  ("54170236", 8),
  ("41702356", 8),
  ("17023546", 8),
  ("70235416", 8),
  ("02354176", 8),
  ("23541706", 6),
  ("62354107", 6),
  ("76235401", 8),
  ("62354071", 8),
  ("23540761", 8),
  ("35407621", 8),
  ("54076231", 6),
  ("15407632", 8),
  ("54076312", 8),
  ("40763152", 8),
  ("07631542", 6),
  ("20763145", 8),
  ("07631425", 8),
  ("76314205", 8),
  ("63142075", 8),
  ("31420765", 6),
  ("53142067", 6),
  ("75314260", 8),
  ("53142670", 8)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 16 := by decide

theorem based07 : basedOnCheck (List.range 8) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("75063412", 8)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("31426750", 8)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("31426750", 8),
  ("14267530", 8),
  ("42675310", 6),
  ("04267513", 8),
  ("42675103", 8),
  ("26751043", 8),
  ("67510423", 6),
  ("36751024", 8),
  ("67510234", 8),
  ("75102364", 6),
  ("47510263", 8),
  ("75102643", 8),
  ("51026473", 8),
  ("10264753", 8),
  ("02647513", 6),
  ("30264715", 8),
  ("02647135", 8),
  ("26471305", 8),
  ("64713025", 8),
  ("47130265", 6),
  ("54713062", 8),
  ("47130652", 8),
  ("71306542", 8),
  ("13065472", 8),
  ("30654712", 6),
  ("23065417", 6),
  ("72306514", 8),
  ("23065174", 8),
  ("30651724", 8),
  ("06517234", 8),
  ("65172304", 6),
  ("46517203", 8)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 16 := by decide

theorem based08 : basedOnCheck (List.range 8) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("31426750", 8)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("65172043", 8)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("65172043", 8),
  ("51720463", 8),
  ("17204653", 6),
  ("31720456", 8),
  ("17204536", 8),
  ("72045316", 8),
  ("20453176", 8),
  ("04531726", 6),
  ("60453127", 6),
  ("76045321", 8),
  ("60453271", 8),
  ("04532761", 8),
  ("45327601", 8),
  ("53276041", 6),
  ("15327640", 8),
  ("53276410", 8),
  ("32764150", 6),
  ("03276451", 8),
  ("32764501", 8),
  ("27645031", 8),
  ("76450321", 6),
  ("17645023", 8),
  ("76450213", 8),
  ("64502173", 8),
  ("45021763", 8),
  ("50217643", 8),
  ("02176453", 6),
  ("30217654", 8),
  ("02176534", 8),
  ("21765304", 8),
  ("17653024", 6),
  ("41765320", 8)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 16 := by decide

theorem based09 : basedOnCheck (List.range 8) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("65172043", 8)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("17653240", 8)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("17653240", 8),
  ("76532410", 8),
  ("65324170", 8),
  ("53241760", 6),
  ("05324167", 6),
  ("70532461", 8),
  ("05324671", 8),
  ("53246701", 8),
  ("32467051", 8),
  ("24670531", 6),
  ("12467035", 8),
  ("24670315", 8),
  ("46703125", 6),
  ("54670321", 8),
  ("46703251", 8),
  ("67032541", 8),
  ("70325461", 8),
  ("03254671", 8),
  ("32546701", 6),
  ("13254607", 6),
  ("71325406", 8),
  ("13254076", 8),
  ("32540716", 8),
  ("25407136", 8),
  ("54071326", 6),
  ("65407123", 8),
  ("54071263", 8),
  ("40712653", 8),
  ("07126543", 6),
  ("30712645", 8),
  ("07126435", 8),
  ("71264305", 8)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 16 := by decide

theorem based10 : basedOnCheck (List.range 8) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("17653240", 8)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("12643075", 8)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("12643075", 8),
  ("26430715", 6),
  ("52643017", 6),
  ("75264310", 8),
  ("52643170", 8),
  ("26431750", 8),
  ("64317520", 8),
  ("43175260", 6),
  ("04317562", 8),
  ("43175602", 8),
  ("31756042", 6),
  ("23175640", 8),
  ("31756420", 8),
  ("17564230", 8),
  ("75642310", 6),
  ("07564213", 8),
  ("75642103", 8),
  ("56421073", 8),
  ("64210753", 8),
  ("42107563", 8),
  ("21075643", 6),
  ("32107546", 8),
  ("21075436", 8),
  ("10754326", 8),
  ("07543216", 6),
  ("60754312", 8),
  ("07543162", 8),
  ("75431602", 8),
  ("54316072", 8),
  ("43160752", 6),
  ("24316057", 6),
  ("72431650", 8)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 18 := by decide

theorem based11 : basedOnCheck (List.range 8) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("12643075", 8)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("24316570", 8)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("24316570", 8),
  ("43165720", 8),
  ("31657240", 8),
  ("16572430", 6),
  ("01657234", 8),
  ("16572304", 8),
  ("65723014", 8),
  ("57230164", 6),
  ("45723061", 8),
  ("57230641", 8),
  ("72306451", 8),
  ("23064571", 8),
  ("30645721", 6),
  ("13064527", 6),
  ("71306425", 8),
  ("13064275", 8),
  ("30642715", 8),
  ("06427135", 6),
  ("50642731", 8),
  ("06427351", 8),
  ("64273501", 8),
  ("42735061", 6),
  ("14273560", 8),
  ("42735610", 8),
  ("27356140", 8),
  ("73561420", 8),
  ("35614270", 8),
  ("56142730", 6),
  ("05614237", 6),
  ("70561432", 8),
  ("05614372", 8),
  ("56143702", 8)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 16 := by decide

theorem based12 : basedOnCheck (List.range 8) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("24316570", 8)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("61437052", 8)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("61437052", 8),
  ("14370562", 6),
  ("21437065", 8),
  ("14370625", 8),
  ("43706215", 6),
  ("54370612", 8),
  ("43706152", 8),
  ("37061542", 8),
  ("70615432", 8),
  ("06154372", 8),
  ("61543702", 6),
  ("26154307", 6),
  ("72615403", 8),
  ("26154073", 8),
  ("61540723", 8),
  ("15407263", 8),
  ("54072613", 6),
  ("35407216", 8),
  ("54072136", 8),
  ("40721356", 6),
  ("64072153", 8),
  ("40721563", 8),
  ("07215643", 8),
  ("72156403", 6),
  ("37215604", 8),
  ("72156034", 8),
  ("21560374", 8),
  ("15603724", 8),
  ("56037214", 8),
  ("60372154", 6),
  ("46037251", 8),
  ("60372541", 8)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 16 := by decide

theorem based13 : basedOnCheck (List.range 8) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("61437052", 8)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("03725461", 8)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("03725461", 8),
  ("37254601", 6),
  ("13725406", 8),
  ("37254016", 8),
  ("72540136", 8),
  ("25401376", 8),
  ("54013726", 6),
  ("65401327", 6),
  ("76540123", 8),
  ("65401273", 8),
  ("54012763", 8),
  ("40127653", 8),
  ("01276543", 6),
  ("30127645", 8),
  ("01276435", 8),
  ("12764305", 8),
  ("27643015", 6),
  ("52764310", 8),
  ("27643150", 8),
  ("76431520", 8),
  ("64315270", 8),
  ("43152760", 6),
  ("04315267", 6),
  ("70431562", 8),
  ("04315672", 8),
  ("43156702", 8),
  ("31567042", 6),
  ("23156740", 8),
  ("31567420", 8),
  ("15674230", 8),
  ("56742310", 6),
  ("05674213", 8)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 18 := by decide

theorem based14 : basedOnCheck (List.range 8) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("03725461", 8)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("56742103", 8)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("56742103", 8),
  ("67421053", 8),
  ("74210563", 8),
  ("42105673", 8),
  ("21056743", 6),
  ("32105647", 6),
  ("73210546", 8),
  ("32105476", 8),
  ("21054736", 8),
  ("10547326", 8),
  ("05473216", 6),
  ("60547312", 8),
  ("05473162", 8),
  ("54731602", 8),
  ("47316052", 6),
  ("24731650", 8),
  ("47316520", 8),
  ("73165240", 8),
  ("31652470", 8),
  ("16524730", 6),
  ("01652437", 6),
  ("70165234", 8),
  ("01652374", 8),
  ("16523704", 8),
  ("65237014", 8),
  ("52370164", 6),
  ("45237061", 8),
  ("52370641", 8),
  ("23706451", 8),
  ("37064521", 6),
  ("13706425", 8),
  ("37064215", 8)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 32 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 16 := by decide

theorem based15 : basedOnCheck (List.range 8) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("56742103", 8)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("70642135", 6)) = true := by rfl

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

theorem rows_charge : (rows.map Row.charge).sum = 264 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, charge08, charge09, charge10, charge11, charge12, charge13, charge14, charge15, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 8) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, based08, based09, based10, based11, based12, based13, based14, based15, Bool.and_self]

def suffix15 : List (Row Nat) := rows15

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("56742103", 8)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("70642135", 6)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("03725461", 8)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("61437052", 8)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("24316570", 8)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("12643075", 8)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("17653240", 8)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("65172043", 8)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("31426750", 8)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("75063412", 8)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("20154763", 6)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("70462153", 8)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("53714026", 8)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("21567034", 8)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("36420517", 6)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("37256104", 8)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("62473105", 8)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("70642135", 6)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("62473105", 8)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("70642135", 6)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.Halfar1Parts.C01
