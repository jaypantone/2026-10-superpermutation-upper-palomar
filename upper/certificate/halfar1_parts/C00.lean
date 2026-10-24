module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original Halfar1 rows 0 through 511.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.Halfar1Parts.C00
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("60123457", 6),
  ("76012354", 8),
  ("60123574", 8),
  ("01235764", 8),
  ("12357604", 6),
  ("41235706", 8),
  ("12357046", 8),
  ("23570416", 8),
  ("35704126", 6),
  ("63570421", 8),
  ("35704261", 8),
  ("57042631", 8),
  ("70426351", 8),
  ("04263571", 8),
  ("42635701", 6),
  ("14263507", 6),
  ("71426305", 8),
  ("14263075", 8),
  ("42630715", 8),
  ("26307145", 8),
  ("63071425", 6),
  ("56307124", 8),
  ("63071254", 8),
  ("30712564", 8),
  ("07125634", 6),
  ("40712536", 8),
  ("07125346", 8),
  ("71253406", 8),
  ("12534076", 8),
  ("25340716", 6),
  ("62534017", 6),
  ("76253410", 8)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 18 := by decide

theorem based00 : basedOnCheck (List.range 8) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("60123457", 6)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("62534170", 8)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("62534170", 8),
  ("25341760", 8),
  ("53417620", 8),
  ("34176250", 6),
  ("03417652", 8),
  ("34176502", 8),
  ("41765032", 8),
  ("17650342", 6),
  ("21765043", 8),
  ("17650423", 8),
  ("76504213", 6),
  ("37650412", 8),
  ("76504132", 8),
  ("65041372", 8),
  ("50413762", 8),
  ("04137652", 6),
  ("20413756", 8),
  ("04137526", 8),
  ("41375206", 8),
  ("13752046", 8),
  ("37520416", 6),
  ("63752014", 8),
  ("37520164", 8),
  ("75201634", 8),
  ("52016374", 8),
  ("20163754", 6),
  ("42016357", 6),
  ("74201653", 8),
  ("42016573", 8),
  ("20165743", 8),
  ("01657423", 8),
  ("16574203", 6)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 16 := by decide

theorem based01 : basedOnCheck (List.range 8) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("62534170", 8)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("31657402", 8)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("31657402", 8),
  ("16574032", 8),
  ("65740312", 8),
  ("57403162", 6),
  ("25740361", 8),
  ("57403621", 8),
  ("74036251", 6),
  ("17403652", 8),
  ("74036512", 8),
  ("40365172", 8),
  ("03651742", 8),
  ("36517402", 8),
  ("65174032", 6),
  ("26517430", 8),
  ("65174320", 8),
  ("51743260", 8),
  ("17432650", 6),
  ("01743256", 8),
  ("17432506", 8),
  ("74325016", 8),
  ("43250176", 8),
  ("32501746", 6),
  ("63250147", 6),
  ("76325041", 8),
  ("63250471", 8),
  ("32504761", 8),
  ("25047631", 8),
  ("50476321", 6),
  ("15047623", 8),
  ("50476213", 8),
  ("04762153", 8),
  ("47621503", 6)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 16 := by decide

theorem based02 : basedOnCheck (List.range 8) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("31657402", 8)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("34762105", 8)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("34762105", 8),
  ("47621035", 8),
  ("76210345", 6),
  ("57621043", 8),
  ("76210453", 8),
  ("62104573", 8),
  ("21045763", 8),
  ("10457623", 6),
  ("31045726", 8),
  ("10457236", 8),
  ("04572316", 8),
  ("45723106", 8),
  ("57231046", 6),
  ("65723140", 8),
  ("57231460", 8),
  ("72314650", 8),
  ("23146570", 8),
  ("31465720", 6),
  ("03146527", 6),
  ("70314625", 8),
  ("03146275", 8),
  ("31462705", 8),
  ("14627035", 8),
  ("46270315", 6),
  ("54627013", 8),
  ("46270153", 8),
  ("62701543", 8),
  ("27015463", 6),
  ("32701564", 8),
  ("27015634", 8),
  ("70156324", 6),
  ("47015623", 8)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 16 := by decide

theorem based03 : basedOnCheck (List.range 8) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("34762105", 8)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("70156243", 8)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("70156243", 8),
  ("01562473", 8),
  ("15624703", 8),
  ("56247013", 8),
  ("62470153", 6),
  ("36247051", 8),
  ("62470531", 8),
  ("24705361", 8),
  ("47053621", 6),
  ("14705326", 8),
  ("47053216", 8),
  ("70532146", 8),
  ("05321476", 8),
  ("53214706", 6),
  ("65321407", 6),
  ("76532104", 8),
  ("65321074", 8),
  ("53210764", 8),
  ("32107654", 8),
  ("21076534", 6),
  ("42107635", 8),
  ("21076345", 8),
  ("10763425", 8),
  ("07634215", 6),
  ("50763412", 8),
  ("07634152", 8),
  ("76341502", 6),
  ("27634105", 8),
  ("76341025", 8),
  ("63410275", 8),
  ("34102765", 8),
  ("41027635", 6)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 16 := by decide

theorem based04 : basedOnCheck (List.range 8) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("70156243", 8)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("54102736", 8)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("54102736", 8),
  ("41027356", 8),
  ("10273546", 8),
  ("02735416", 8),
  ("27354106", 6),
  ("62735401", 8),
  ("27354061", 8),
  ("73540621", 8),
  ("35406271", 8),
  ("54062731", 6),
  ("15406237", 6),
  ("71540632", 8),
  ("15406372", 8),
  ("54063712", 8),
  ("40637152", 8),
  ("06371542", 6),
  ("20637145", 8),
  ("06371425", 8),
  ("63714205", 8),
  ("37142065", 6),
  ("53714260", 8),
  ("37142650", 8),
  ("71426530", 8),
  ("14265370", 8),
  ("42653710", 6),
  ("04265317", 6),
  ("70426513", 8),
  ("04265173", 8),
  ("42651703", 8),
  ("26517043", 8),
  ("65170423", 6),
  ("36517024", 8)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 16 := by decide

theorem based05 : basedOnCheck (List.range 8) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("54102736", 8)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("65170234", 8)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("65170234", 8),
  ("51702364", 6),
  ("45170263", 8),
  ("51702643", 8),
  ("17026453", 8),
  ("70264513", 6),
  ("37026415", 8),
  ("70264135", 8),
  ("02641375", 8),
  ("26413705", 8),
  ("64137025", 8),
  ("41370265", 6),
  ("54137062", 8),
  ("41370652", 8),
  ("13706542", 8),
  ("37065412", 6),
  ("23706514", 8),
  ("37065124", 8),
  ("70651234", 8),
  ("06512374", 8),
  ("65123704", 6),
  ("46512307", 6),
  ("74651203", 8),
  ("46512073", 8),
  ("65120743", 8),
  ("51207463", 8),
  ("12074653", 6),
  ("31207456", 8),
  ("12074536", 8),
  ("20745316", 8),
  ("07453126", 6),
  ("60745321", 8)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 16 := by decide

theorem based06 : basedOnCheck (List.range 8) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("65170234", 8)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("07453261", 8)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("07453261", 8),
  ("74532601", 8),
  ("45326071", 8),
  ("53260741", 6),
  ("15326047", 6),
  ("71532640", 8),
  ("15326470", 8),
  ("53264710", 8),
  ("32647150", 6),
  ("03264751", 8),
  ("32647501", 8),
  ("26475031", 8),
  ("64750321", 6),
  ("16475023", 8),
  ("64750213", 8),
  ("47502163", 8),
  ("75021643", 8),
  ("50216473", 8),
  ("02164753", 6),
  ("30216457", 6),
  ("73021654", 8),
  ("30216574", 8),
  ("02165734", 8),
  ("21657304", 8),
  ("16573024", 6),
  ("41657320", 8),
  ("16573240", 8),
  ("65732410", 8),
  ("57324160", 6),
  ("05732461", 8),
  ("57324601", 8),
  ("73246051", 8)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 16 := by decide

theorem based07 : basedOnCheck (List.range 8) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("07453261", 8)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("32460571", 8)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("32460571", 8),
  ("24605731", 6),
  ("12460537", 6),
  ("71246035", 8),
  ("12460375", 8),
  ("24603715", 8),
  ("46037125", 8),
  ("60371245", 6),
  ("56037142", 8),
  ("60371452", 8),
  ("03714562", 8),
  ("37145602", 6),
  ("23714506", 8),
  ("37145026", 8),
  ("71450236", 6),
  ("67145032", 8),
  ("71450362", 8),
  ("14503672", 8),
  ("45036712", 8),
  ("50367142", 6),
  ("25036741", 8),
  ("50367421", 8),
  ("03674251", 8),
  ("36742501", 8),
  ("67425031", 6),
  ("16742530", 8),
  ("67425310", 8),
  ("74253160", 8),
  ("42531670", 8),
  ("25316740", 6),
  ("02531647", 6),
  ("70253146", 8)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 18 := by decide

theorem based08 : basedOnCheck (List.range 8) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("32460571", 8)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("02531476", 8)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("02531476", 8),
  ("25314706", 8),
  ("53147026", 8),
  ("31470256", 6),
  ("63147052", 8),
  ("31470562", 8),
  ("14705632", 8),
  ("47056312", 6),
  ("24705613", 8),
  ("47056123", 8),
  ("70561243", 8),
  ("05612473", 8),
  ("56124703", 6),
  ("35612407", 6),
  ("73561204", 8),
  ("35612074", 8),
  ("56120734", 8),
  ("61207354", 8),
  ("12073564", 6),
  ("41207365", 8),
  ("12073645", 8),
  ("20736415", 6),
  ("52073614", 8),
  ("20736154", 8),
  ("07361524", 8),
  ("73615204", 6),
  ("47361502", 8),
  ("73615042", 8),
  ("36150472", 8),
  ("61504732", 8),
  ("15047362", 8),
  ("50473612", 6)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 16 := by decide

theorem based09 : basedOnCheck (List.range 8) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("02531476", 8)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("25047316", 8)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("25047316", 8),
  ("50473126", 8),
  ("04731256", 8),
  ("47312506", 6),
  ("64731205", 8),
  ("47312065", 8),
  ("73120645", 8),
  ("31206475", 8),
  ("12064735", 6),
  ("51206437", 6),
  ("75120634", 8),
  ("51206374", 8),
  ("12063754", 8),
  ("20637514", 8),
  ("06375124", 6),
  ("40637521", 8),
  ("06375241", 8),
  ("63752401", 8),
  ("37524061", 6),
  ("13752460", 8),
  ("37524610", 8),
  ("75246130", 8),
  ("52461370", 8),
  ("24613750", 6),
  ("02461357", 6),
  ("70246153", 8),
  ("02461573", 8),
  ("24615703", 8),
  ("46157023", 6),
  ("34615720", 8),
  ("46157230", 8),
  ("61572340", 8)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 16 := by decide

theorem based10 : basedOnCheck (List.range 8) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("25047316", 8)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("15723460", 6)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("15723460", 6),
  ("01572364", 8),
  ("15723604", 8),
  ("57236014", 8),
  ("72360154", 8),
  ("23601574", 8),
  ("36015724", 6),
  ("43601527", 6),
  ("74360125", 8),
  ("43601275", 8),
  ("36012745", 8),
  ("60127435", 8),
  ("01274365", 6),
  ("50127463", 8),
  ("01274653", 8),
  ("12746503", 8),
  ("27465013", 6),
  ("32746510", 8),
  ("27465130", 8),
  ("74651320", 8),
  ("46513270", 8),
  ("65132740", 6),
  ("06513247", 6),
  ("70651342", 8),
  ("06513472", 8),
  ("65134702", 8),
  ("51347062", 8),
  ("13470652", 6),
  ("21347056", 8),
  ("13470526", 8),
  ("34705216", 8),
  ("47052136", 6)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 18 := by decide

theorem based11 : basedOnCheck (List.range 8) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("15723460", 6)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("64705231", 8)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("64705231", 8),
  ("47052361", 8),
  ("70523641", 6),
  ("17052346", 8),
  ("70523416", 8),
  ("05234176", 8),
  ("52341706", 8),
  ("23417056", 6),
  ("62341750", 8),
  ("23417560", 8),
  ("34175620", 8),
  ("41756230", 6),
  ("04175632", 8),
  ("41756302", 8),
  ("17563042", 8),
  ("75630412", 8),
  ("56304172", 8),
  ("63041752", 6),
  ("26304157", 6),
  ("72630451", 8),
  ("26304571", 8),
  ("63045721", 8),
  ("30457261", 6),
  ("13045762", 8),
  ("30457612", 8),
  ("04576132", 8),
  ("45761302", 6),
  ("24576103", 8),
  ("45761023", 8),
  ("57610243", 8),
  ("76102453", 6),
  ("37610254", 8)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 16 := by decide

theorem based12 : basedOnCheck (List.range 8) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("64705231", 8)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("76102534", 8)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("76102534", 8),
  ("61025374", 8),
  ("10253764", 8),
  ("02537614", 8),
  ("25376104", 6),
  ("42537601", 8),
  ("25376041", 8),
  ("53760421", 8),
  ("37604251", 6),
  ("13760452", 8),
  ("37604512", 8),
  ("76045132", 8),
  ("60451372", 8),
  ("04513762", 6),
  ("20451367", 6),
  ("72045163", 8),
  ("20451673", 8),
  ("04516723", 8),
  ("45167203", 8),
  ("51672043", 6),
  ("35167240", 8),
  ("51672430", 8),
  ("16724350", 8),
  ("67243510", 6),
  ("06724315", 8),
  ("67243105", 8),
  ("72431065", 8),
  ("24310675", 8),
  ("43106725", 6),
  ("54310627", 6),
  ("75431026", 8),
  ("54310276", 8)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 16 := by decide

theorem based13 : basedOnCheck (List.range 8) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("76102534", 8)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("43102756", 8)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("43102756", 8),
  ("31027546", 6),
  ("63102745", 8),
  ("31027465", 8),
  ("10274635", 8),
  ("02746315", 8),
  ("27463105", 6),
  ("52746301", 8),
  ("27463051", 8),
  ("74630521", 8),
  ("46305271", 8),
  ("63052741", 6),
  ("16305247", 6),
  ("71630542", 8),
  ("16305472", 8),
  ("63054712", 8),
  ("30547162", 8),
  ("05471632", 6),
  ("20547136", 8),
  ("05471326", 8),
  ("54713206", 8),
  ("47132056", 6),
  ("64713250", 8),
  ("47132560", 8),
  ("71325640", 8),
  ("13256470", 8),
  ("32564710", 6),
  ("03256417", 6),
  ("70325614", 8),
  ("03256174", 8),
  ("32561704", 8),
  ("25617034", 8)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 16 := by decide

theorem based14 : basedOnCheck (List.range 8) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("43102756", 8)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("56170324", 6)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("56170324", 6),
  ("45617023", 8),
  ("56170243", 8),
  ("61702453", 6),
  ("36170254", 8),
  ("61702534", 8),
  ("17025364", 8),
  ("70253614", 8),
  ("02536174", 8),
  ("25361704", 6),
  ("42536107", 6),
  ("74253601", 8),
  ("42536071", 8),
  ("25360741", 8),
  ("53607421", 8),
  ("36074251", 6),
  ("13607452", 8),
  ("36074512", 8),
  ("60745132", 8),
  ("07451362", 6),
  ("20745163", 8),
  ("07451623", 8),
  ("74516203", 8),
  ("45162073", 8),
  ("51620743", 6),
  ("35162047", 6),
  ("73516240", 8),
  ("35162470", 8),
  ("51624730", 8),
  ("16247350", 8),
  ("62473510", 6),
  ("06247315", 8)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 32 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 18 := by decide

theorem based15 : basedOnCheck (List.range 8) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("56170324", 6)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("62473105", 8)) = true := by rfl

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

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("56170324", 6)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("62473105", 8)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("43102756", 8)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("76102534", 8)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("64705231", 8)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("15723460", 6)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("25047316", 8)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("02531476", 8)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("32460571", 8)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("07453261", 8)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("65170234", 8)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("54102736", 8)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("70156243", 8)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("34762105", 8)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("31657402", 8)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("62534170", 8)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("60123457", 6)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("62473105", 8)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("60123457", 6)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("62473105", 8)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.Halfar1Parts.C00
