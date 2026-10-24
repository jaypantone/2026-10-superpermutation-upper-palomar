module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original Halfar0 rows 512 through 1023.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.Halfar0Parts.C01
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("30765412", 6),
  ("23076514", 8),
  ("30765124", 8),
  ("07651234", 8),
  ("76512304", 6),
  ("47651203", 8),
  ("76512043", 8),
  ("65120473", 8),
  ("51204763", 8),
  ("12047653", 6),
  ("31204756", 8),
  ("12047536", 8),
  ("20475316", 8),
  ("04753126", 6),
  ("60475321", 8),
  ("04753261", 8),
  ("47532601", 8),
  ("75326041", 6),
  ("17532640", 8),
  ("75326410", 8),
  ("53264170", 8),
  ("32641750", 6),
  ("03264157", 6),
  ("70326451", 8),
  ("03264571", 8),
  ("32645701", 8),
  ("26457031", 8),
  ("64570321", 6),
  ("16457023", 8),
  ("64570213", 8),
  ("45702163", 8),
  ("57021643", 8)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 16 := by decide

theorem based00 : basedOnCheck (List.range 8) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("30765412", 6)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("70216453", 6)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("70216453", 6),
  ("37021654", 8),
  ("70216534", 8),
  ("02165374", 8),
  ("21653704", 8),
  ("16537024", 6),
  ("41653720", 8),
  ("16537240", 8),
  ("65372410", 8),
  ("53724160", 6),
  ("05372461", 8),
  ("53724601", 8),
  ("37246051", 8),
  ("72460531", 6),
  ("17246035", 8),
  ("72460315", 8),
  ("24603175", 8),
  ("46031725", 8),
  ("60317245", 6),
  ("56031742", 8),
  ("60317452", 8),
  ("03174562", 8),
  ("31745602", 6),
  ("23174506", 8),
  ("31745026", 8),
  ("17450236", 6),
  ("61745032", 8),
  ("17450362", 8),
  ("74503612", 8),
  ("45036172", 8),
  ("50361742", 6),
  ("25036147", 6)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 18 := by decide

theorem based01 : basedOnCheck (List.range 8) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("70216453", 6)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("72503641", 8)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("72503641", 8),
  ("25036471", 8),
  ("50364721", 8),
  ("03647251", 8),
  ("36472501", 8),
  ("64725031", 6),
  ("16472530", 8),
  ("64725310", 8),
  ("47253160", 8),
  ("72531640", 6),
  ("07253146", 8),
  ("72531406", 8),
  ("25314076", 8),
  ("53140726", 8),
  ("31407256", 6),
  ("63140752", 8),
  ("31407562", 8),
  ("14075632", 8),
  ("40756312", 6),
  ("24075613", 8),
  ("40756123", 8),
  ("07561243", 8),
  ("75612403", 6),
  ("37561204", 8),
  ("75612034", 8),
  ("56120374", 8),
  ("61203754", 8),
  ("12037564", 6),
  ("41203765", 8),
  ("12037645", 8),
  ("20376415", 6),
  ("52037614", 8)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 14 := by decide

theorem based02 : basedOnCheck (List.range 8) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("72503641", 8)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("20376154", 8)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("20376154", 8),
  ("03761524", 8),
  ("37615204", 6),
  ("43761502", 8),
  ("37615042", 8),
  ("76150432", 8),
  ("61504372", 8),
  ("15043762", 8),
  ("50437612", 6),
  ("25043716", 8),
  ("50437126", 8),
  ("04371256", 8),
  ("43712506", 6),
  ("64371205", 8),
  ("43712065", 8),
  ("37120645", 8),
  ("71206435", 6),
  ("57120634", 8),
  ("71206354", 8),
  ("12063574", 8),
  ("20635714", 8),
  ("06357124", 6),
  ("40635721", 8),
  ("06357241", 8),
  ("63572401", 8),
  ("35724061", 6),
  ("13572460", 8),
  ("35724610", 8),
  ("57246130", 8),
  ("72461350", 6),
  ("07246153", 8),
  ("72461503", 8)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 14 := by decide

theorem based03 : basedOnCheck (List.range 8) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("20376154", 8)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("24615073", 8)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("24615073", 8),
  ("46150723", 6),
  ("34615027", 6),
  ("73461520", 8),
  ("34615270", 8),
  ("46152730", 8),
  ("61527340", 8),
  ("15273460", 6),
  ("01527364", 8),
  ("15273604", 8),
  ("52736014", 8),
  ("27360154", 8),
  ("73601524", 6),
  ("47360125", 8),
  ("73601245", 8),
  ("36012475", 8),
  ("60124735", 8),
  ("01247365", 6),
  ("50124763", 8),
  ("01247653", 8),
  ("12476503", 8),
  ("24765013", 6),
  ("32476510", 8),
  ("24765130", 8),
  ("47651320", 8),
  ("76513240", 6),
  ("07651342", 8),
  ("76513402", 8),
  ("65134072", 8),
  ("51340762", 8),
  ("13407652", 6),
  ("21340756", 8)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 16 := by decide

theorem based04 : basedOnCheck (List.range 8) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("24615073", 8)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("13407526", 8)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("13407526", 8),
  ("34075216", 8),
  ("40752136", 6),
  ("64075231", 8),
  ("40752361", 8),
  ("07523641", 6),
  ("10752346", 8),
  ("07523416", 8),
  ("75234106", 8),
  ("52341076", 8),
  ("23410756", 6),
  ("62341057", 6),
  ("76234150", 8),
  ("62341570", 8),
  ("23415760", 8),
  ("34157620", 8),
  ("41576230", 6),
  ("04157632", 8),
  ("41576302", 8),
  ("15763042", 8),
  ("57630412", 8),
  ("76304152", 6),
  ("27630451", 8),
  ("76304521", 8),
  ("63045271", 8),
  ("30452761", 6),
  ("13045267", 6),
  ("71304562", 8),
  ("13045672", 8),
  ("30456712", 8),
  ("04567132", 8),
  ("45671302", 6)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 18 := by decide

theorem based05 : basedOnCheck (List.range 8) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("13407526", 8)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("24567103", 8)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("24567103", 8),
  ("45671023", 8),
  ("56710243", 8),
  ("67102453", 6),
  ("36710254", 8),
  ("67102534", 8),
  ("71025364", 8),
  ("10253674", 8),
  ("02536714", 8),
  ("25367104", 6),
  ("42536701", 8),
  ("25367041", 8),
  ("53670421", 8),
  ("36704251", 6),
  ("13670452", 8),
  ("36704512", 8),
  ("67045132", 8),
  ("70451362", 6),
  ("27045163", 8),
  ("70451623", 8),
  ("04516273", 8),
  ("45162703", 8),
  ("51627043", 6),
  ("35162740", 8),
  ("51627430", 8),
  ("16274350", 8),
  ("62743510", 6),
  ("06274315", 8),
  ("62743105", 8),
  ("27431065", 8),
  ("74310625", 6),
  ("57431026", 8)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 14 := by decide

theorem based06 : basedOnCheck (List.range 8) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("24567103", 8)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("74310256", 8)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("74310256", 8),
  ("43102576", 8),
  ("31025746", 6),
  ("63102547", 6),
  ("76310245", 8),
  ("63102475", 8),
  ("31024765", 8),
  ("10247635", 8),
  ("02476315", 8),
  ("24763105", 6),
  ("52476301", 8),
  ("24763051", 8),
  ("47630521", 8),
  ("76305241", 6),
  ("17630542", 8),
  ("76305412", 8),
  ("63054172", 8),
  ("30541762", 8),
  ("05417632", 6),
  ("20541736", 8),
  ("05417326", 8),
  ("54173206", 8),
  ("41732056", 6),
  ("64173250", 8),
  ("41732560", 8),
  ("17325640", 8),
  ("73256410", 6),
  ("07325614", 8),
  ("73256104", 8),
  ("32561074", 8),
  ("25610734", 6),
  ("42561037", 6)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 18 := by decide

theorem based07 : basedOnCheck (List.range 8) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("74310256", 8)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("74256130", 8)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("74256130", 8),
  ("42561370", 8),
  ("25613740", 8),
  ("56137420", 8),
  ("61374250", 6),
  ("06137452", 8),
  ("61374502", 8),
  ("13745062", 8),
  ("37450612", 8),
  ("74506132", 6),
  ("27450631", 8),
  ("74506321", 8),
  ("45063271", 8),
  ("50632741", 8),
  ("06327451", 6),
  ("10632754", 8),
  ("06327514", 8),
  ("63275104", 8),
  ("32751064", 6),
  ("43275160", 8),
  ("32751640", 8),
  ("27516430", 8),
  ("75164320", 6),
  ("07516423", 8),
  ("75164203", 8),
  ("51642073", 8),
  ("16420753", 8),
  ("64207513", 6),
  ("36420715", 8),
  ("64207135", 8),
  ("42071365", 8),
  ("20713645", 6)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 14 := by decide

theorem based08 : basedOnCheck (List.range 8) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("74256130", 8)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("52071346", 8)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("52071346", 8),
  ("20713456", 8),
  ("07134526", 6),
  ("60713425", 8),
  ("07134265", 8),
  ("71342605", 8),
  ("13426075", 8),
  ("34260715", 6),
  ("53426017", 6),
  ("75342610", 8),
  ("53426170", 8),
  ("34261750", 8),
  ("42617530", 8),
  ("26175340", 8),
  ("61753420", 6),
  ("06175324", 8),
  ("61753204", 8),
  ("17532064", 8),
  ("75320614", 6),
  ("47532016", 8),
  ("75320146", 8),
  ("53201476", 8),
  ("32014756", 8),
  ("20147536", 6),
  ("62014735", 8),
  ("20147365", 8),
  ("01473625", 8),
  ("14736205", 6),
  ("51473602", 8),
  ("14736052", 8),
  ("47360512", 8),
  ("73605142", 6)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 16 := by decide

theorem based09 : basedOnCheck (List.range 8) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("52071346", 8)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("27360541", 8)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("27360541", 8),
  ("73605421", 8),
  ("36054271", 8),
  ("60542731", 8),
  ("05427361", 6),
  ("10542763", 8),
  ("05427613", 8),
  ("54276103", 6),
  ("35427601", 8),
  ("54276031", 8),
  ("42760351", 8),
  ("27603541", 6),
  ("12760345", 8),
  ("27603415", 8),
  ("76034125", 8),
  ("60341275", 8),
  ("03412765", 8),
  ("34127605", 6),
  ("53412706", 8),
  ("34127056", 8),
  ("41270536", 8),
  ("12705346", 6),
  ("61270543", 8),
  ("12705463", 8),
  ("27054613", 8),
  ("70546123", 6),
  ("37054621", 8),
  ("70546231", 8),
  ("05462371", 8),
  ("54623701", 8),
  ("46237051", 6),
  ("14623750", 8)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 14 := by decide

theorem based10 : basedOnCheck (List.range 8) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("27360541", 8)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("46237510", 8)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("46237510", 8),
  ("62375140", 8),
  ("23751460", 6),
  ("02375164", 8),
  ("23751604", 8),
  ("37516024", 8),
  ("75160234", 6),
  ("47516032", 8),
  ("75160342", 8),
  ("51603472", 8),
  ("16034752", 6),
  ("21603457", 6),
  ("72160354", 8),
  ("21603574", 8),
  ("16035724", 8),
  ("60357214", 8),
  ("03572164", 6),
  ("40357261", 8),
  ("03572641", 8),
  ("35726401", 8),
  ("57264031", 8),
  ("72640351", 6),
  ("17264053", 8),
  ("72640513", 8),
  ("26405173", 8),
  ("64051723", 8),
  ("40517263", 6),
  ("34051762", 8),
  ("40517632", 8),
  ("05176342", 8),
  ("51763402", 6),
  ("25176304", 8)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 16 := by decide

theorem based11 : basedOnCheck (List.range 8) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("46237510", 8)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("51763024", 8)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("51763024", 8),
  ("17630254", 8),
  ("76302514", 6),
  ("47630215", 8),
  ("76302145", 8),
  ("63021475", 8),
  ("30214765", 8),
  ("02147635", 6),
  ("50214736", 8),
  ("02147356", 8),
  ("21473506", 8),
  ("14735026", 6),
  ("61473520", 8),
  ("14735260", 8),
  ("47352610", 6),
  ("04735216", 8),
  ("47352106", 8),
  ("73521046", 8),
  ("35210476", 8),
  ("52104736", 6),
  ("65210437", 6),
  ("76521034", 8),
  ("65210374", 8),
  ("52103764", 8),
  ("21037654", 8),
  ("10376524", 6),
  ("41037625", 8),
  ("10376245", 8),
  ("03762415", 8),
  ("37624105", 8),
  ("76241035", 6),
  ("57624130", 8)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 16 := by decide

theorem based12 : basedOnCheck (List.range 8) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("51763024", 8)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("76241350", 8)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("76241350", 8),
  ("62413570", 8),
  ("24135760", 6),
  ("02413567", 6),
  ("70241365", 8),
  ("02413675", 8),
  ("24136705", 8),
  ("41367025", 8),
  ("13670245", 8),
  ("36702415", 6),
  ("53670214", 8),
  ("36702154", 8),
  ("67021534", 6),
  ("46702135", 8),
  ("67021345", 8),
  ("70213465", 8),
  ("02134675", 8),
  ("21346705", 8),
  ("13467025", 6),
  ("51346720", 8),
  ("13467250", 8),
  ("34672510", 8),
  ("46725130", 6),
  ("04672531", 8),
  ("46725301", 8),
  ("67253041", 8),
  ("72530461", 6),
  ("17253064", 8),
  ("72530614", 8),
  ("25306174", 8),
  ("53061724", 6),
  ("45306127", 6)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 18 := by decide

theorem based13 : basedOnCheck (List.range 8) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("76241350", 8)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("74530621", 8)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("74530621", 8),
  ("45306271", 8),
  ("53062741", 8),
  ("30627451", 8),
  ("06274531", 8),
  ("62745301", 6),
  ("16274503", 8),
  ("62745013", 8),
  ("27450163", 8),
  ("74501623", 6),
  ("37450126", 8),
  ("74501236", 8),
  ("45012376", 8),
  ("50123746", 8),
  ("01237456", 6),
  ("60123754", 8),
  ("01237564", 8),
  ("12375604", 6),
  ("41237506", 8),
  ("12375046", 8),
  ("23750416", 8),
  ("37504126", 6),
  ("63750421", 8),
  ("37504261", 8),
  ("75042631", 8),
  ("50426371", 8),
  ("04263751", 8),
  ("42637501", 6),
  ("14263705", 8),
  ("42637015", 8),
  ("26370145", 8),
  ("63701425", 6)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 14 := by decide

theorem based14 : basedOnCheck (List.range 8) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("74530621", 8)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("56370124", 8)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("56370124", 8),
  ("63701254", 8),
  ("37012564", 8),
  ("70125634", 6),
  ("47012536", 8),
  ("70125346", 8),
  ("01253476", 8),
  ("12534706", 8),
  ("25347016", 6),
  ("62534710", 8),
  ("25347160", 8),
  ("53471620", 8),
  ("34716250", 6),
  ("03471652", 8),
  ("34716502", 8),
  ("47165032", 8),
  ("71650342", 6),
  ("27165043", 8),
  ("71650423", 8),
  ("16504273", 8),
  ("65042713", 6),
  ("36504217", 6),
  ("73650412", 8),
  ("36504172", 8),
  ("65041732", 8),
  ("50417362", 8),
  ("04173652", 6),
  ("20417356", 8),
  ("04173526", 8),
  ("41735206", 8),
  ("17352046", 8),
  ("73520416", 6)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 32 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 16 := by decide

theorem based15 : basedOnCheck (List.range 8) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("56370124", 8)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("67352014", 8)) = true := by rfl

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

theorem rows_charge : (rows.map Row.charge).sum = 252 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, charge08, charge09, charge10, charge11, charge12, charge13, charge14, charge15, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 8) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, based08, based09, based10, based11, based12, based13, based14, based15, Bool.and_self]

def suffix15 : List (Row Nat) := rows15

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("56370124", 8)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("67352014", 8)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("74530621", 8)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("76241350", 8)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("51763024", 8)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("46237510", 8)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("27360541", 8)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("52071346", 8)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("74256130", 8)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("74310256", 8)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("24567103", 8)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("13407526", 8)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("24615073", 8)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("20376154", 8)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("72503641", 8)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("70216453", 6)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("30765412", 6)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("67352014", 8)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("30765412", 6)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("67352014", 8)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.Halfar0Parts.C01
