module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original Halfar0 rows 1536 through 2047.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.Halfar0Parts.C03
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("14276305", 8),
  ("42763015", 8),
  ("27630145", 8),
  ("76301425", 6),
  ("57630124", 8),
  ("76301254", 8),
  ("63012574", 8),
  ("30125764", 8),
  ("01257634", 6),
  ("40125736", 8),
  ("01257346", 8),
  ("12573406", 8),
  ("25734016", 6),
  ("62573410", 8),
  ("25734160", 8),
  ("57341620", 8),
  ("73416250", 6),
  ("07341652", 8),
  ("73416502", 8),
  ("34165072", 8),
  ("41650732", 8),
  ("16507342", 6),
  ("21650743", 8),
  ("16507423", 8),
  ("65074213", 6),
  ("36507412", 8),
  ("65074132", 8),
  ("50741362", 8),
  ("07413652", 6),
  ("20741356", 8),
  ("07413526", 8),
  ("74135206", 8)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 14 := by decide

theorem based00 : basedOnCheck (List.range 8) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("14276305", 8)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("41352076", 8)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("41352076", 8),
  ("13520746", 8),
  ("35207416", 6),
  ("63520714", 8),
  ("35207164", 8),
  ("52071634", 8),
  ("20716354", 6),
  ("42071653", 8),
  ("20716543", 8),
  ("07165423", 8),
  ("71654203", 6),
  ("37165402", 8),
  ("71654032", 8),
  ("16540372", 8),
  ("65403712", 8),
  ("54037162", 6),
  ("25403761", 8),
  ("54037621", 8),
  ("40376251", 6),
  ("14037652", 8),
  ("40376512", 8),
  ("03765142", 8),
  ("37651402", 8),
  ("76514032", 6),
  ("27651430", 8),
  ("76514320", 8),
  ("65143270", 8),
  ("51432760", 8),
  ("14327650", 6),
  ("01432756", 8),
  ("14327506", 8),
  ("43275016", 8)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 14 := by decide

theorem based01 : basedOnCheck (List.range 8) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("41352076", 8)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("32750146", 6)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("32750146", 6),
  ("63275041", 8),
  ("32750461", 8),
  ("27504631", 8),
  ("75046321", 6),
  ("17504623", 8),
  ("75046213", 8),
  ("50462173", 8),
  ("04621753", 8),
  ("46217503", 6),
  ("34621705", 8),
  ("46217035", 8),
  ("62170345", 6),
  ("56217043", 8),
  ("62170453", 8),
  ("21704563", 8),
  ("17045623", 6),
  ("31704526", 8),
  ("17045236", 8),
  ("70452316", 8),
  ("04523176", 8),
  ("45231706", 8),
  ("52317046", 6),
  ("65231740", 8),
  ("52317460", 8),
  ("23174650", 8),
  ("31746520", 6),
  ("03174625", 8),
  ("31746205", 8),
  ("17462035", 8),
  ("74620315", 6),
  ("57462013", 8)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 16 := by decide

theorem based02 : basedOnCheck (List.range 8) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("32750146", 6)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("74620153", 8)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("74620153", 8),
  ("46201573", 8),
  ("62015743", 8),
  ("20157463", 6),
  ("32015764", 8),
  ("20157634", 8),
  ("01576324", 6),
  ("40157623", 8),
  ("01576243", 8),
  ("15762403", 8),
  ("57624013", 8),
  ("76240153", 6),
  ("37624051", 8),
  ("76240531", 8),
  ("62405371", 8),
  ("24053761", 8),
  ("40537621", 6),
  ("14053726", 8),
  ("40537216", 8),
  ("05372146", 8),
  ("53721406", 6),
  ("65372104", 8),
  ("53721064", 8),
  ("37210654", 8),
  ("72106534", 6),
  ("47210635", 8),
  ("72106345", 8),
  ("21063475", 8),
  ("10634725", 8),
  ("06347215", 6),
  ("50634712", 8),
  ("06347152", 8)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 14 := by decide

theorem based03 : basedOnCheck (List.range 8) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("74620153", 8)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("63471502", 6)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("63471502", 6),
  ("26347105", 8),
  ("63471025", 8),
  ("34710265", 8),
  ("47102635", 6),
  ("54710236", 8),
  ("47102356", 8),
  ("71023546", 8),
  ("10235476", 8),
  ("02354716", 8),
  ("23547106", 6),
  ("62354701", 8),
  ("23547061", 8),
  ("35470621", 8),
  ("54706231", 6),
  ("15470632", 8),
  ("54706312", 8),
  ("47063152", 8),
  ("70631542", 6),
  ("27063145", 8),
  ("70631425", 8),
  ("06314275", 8),
  ("63142705", 8),
  ("31427065", 6),
  ("53142760", 8),
  ("31427650", 8),
  ("14276530", 8),
  ("42765310", 6),
  ("04276513", 8),
  ("42765103", 8),
  ("27651043", 8),
  ("76510423", 6)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 16 := by decide

theorem based04 : basedOnCheck (List.range 8) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("63471502", 6)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("37651024", 8)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("37651024", 8),
  ("76510234", 8),
  ("65102374", 8),
  ("51023764", 6),
  ("45102367", 6),
  ("74510263", 8),
  ("45102673", 8),
  ("51026743", 8),
  ("10267453", 8),
  ("02674513", 6),
  ("30267415", 8),
  ("02674135", 8),
  ("26741305", 8),
  ("67413025", 8),
  ("74130265", 6),
  ("57413062", 8),
  ("74130652", 8),
  ("41306572", 8),
  ("13065742", 8),
  ("30657412", 6),
  ("23065714", 8),
  ("30657124", 8),
  ("06571234", 8),
  ("65712304", 6),
  ("46571203", 8),
  ("65712043", 8),
  ("57120463", 8),
  ("71204653", 6),
  ("37120456", 8),
  ("71204536", 8),
  ("12045376", 8),
  ("20453716", 8)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 14 := by decide

theorem based05 : basedOnCheck (List.range 8) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("37651024", 8)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("04537126", 6)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("04537126", 6),
  ("60453721", 8),
  ("04537261", 8),
  ("45372601", 8),
  ("53726041", 6),
  ("15372640", 8),
  ("53726410", 8),
  ("37264150", 6),
  ("03726451", 8),
  ("37264501", 8),
  ("72645031", 8),
  ("26450371", 8),
  ("64503721", 6),
  ("16450327", 6),
  ("71645023", 8),
  ("16450273", 8),
  ("64502713", 8),
  ("45027163", 8),
  ("50271643", 8),
  ("02716453", 6),
  ("30271654", 8),
  ("02716534", 8),
  ("27165304", 8),
  ("71653024", 6),
  ("47165320", 8),
  ("71653240", 8),
  ("16532470", 8),
  ("65324710", 8),
  ("53247160", 6),
  ("05324761", 8),
  ("53247601", 8),
  ("32476051", 8)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 16 := by decide

theorem based06 : basedOnCheck (List.range 8) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("04537126", 6)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("24760531", 6)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("24760531", 6),
  ("12476035", 8),
  ("24760315", 8),
  ("47603125", 8),
  ("76031245", 6),
  ("57603142", 8),
  ("76031452", 8),
  ("60314572", 8),
  ("03145762", 8),
  ("31457602", 6),
  ("23145706", 8),
  ("31457026", 8),
  ("14570236", 6),
  ("61457032", 8),
  ("14570362", 8),
  ("45703612", 8),
  ("57036142", 6),
  ("25703641", 8),
  ("57036421", 8),
  ("70364251", 8),
  ("03642571", 8),
  ("36425701", 8),
  ("64257031", 6),
  ("16425730", 8),
  ("64257310", 8),
  ("42573160", 8),
  ("25731640", 6),
  ("02573146", 8),
  ("25731406", 8),
  ("57314026", 6),
  ("65731420", 8),
  ("57314260", 8)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 16 := by decide

theorem based07 : basedOnCheck (List.range 8) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("24760531", 6)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("73142650", 8)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("73142650", 8),
  ("31426570", 8),
  ("14265730", 8),
  ("42657310", 6),
  ("04265713", 8),
  ("42657103", 8),
  ("26571043", 6),
  ("32657140", 8),
  ("26571430", 8),
  ("65714320", 8),
  ("57143260", 8),
  ("71432650", 6),
  ("07143256", 8),
  ("71432506", 8),
  ("14325076", 8),
  ("43250716", 8),
  ("32507146", 6),
  ("63250741", 8),
  ("32507461", 8),
  ("25074631", 8),
  ("50746321", 6),
  ("15074623", 8),
  ("50746213", 8),
  ("07462153", 8),
  ("74621503", 6),
  ("37462105", 8),
  ("74621035", 8),
  ("46210375", 8),
  ("62103745", 6),
  ("56210347", 6),
  ("75621043", 8),
  ("56210473", 8)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 16 := by decide

theorem based08 : basedOnCheck (List.range 8) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("73142650", 8)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("62104753", 8)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("62104753", 8),
  ("21047563", 8),
  ("10475623", 6),
  ("31047526", 8),
  ("10475236", 8),
  ("04752316", 8),
  ("47523106", 8),
  ("75231046", 6),
  ("67523140", 8),
  ("75231460", 8),
  ("52314670", 8),
  ("23146750", 8),
  ("31467520", 6),
  ("03146725", 8),
  ("31467205", 8),
  ("14672035", 8),
  ("46720315", 6),
  ("54672013", 8),
  ("46720153", 8),
  ("67201543", 8),
  ("72015463", 6),
  ("37201564", 8),
  ("72015634", 8),
  ("20156374", 8),
  ("01563724", 6),
  ("40156327", 6),
  ("74015623", 8),
  ("40156273", 8),
  ("01562743", 8),
  ("15627403", 8),
  ("56274013", 8),
  ("62740153", 6)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 16 := by decide

theorem based09 : basedOnCheck (List.range 8) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("62104753", 8)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("36274051", 8)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("36274051", 8),
  ("62740531", 8),
  ("27405361", 8),
  ("74053621", 6),
  ("17405326", 8),
  ("74053216", 8),
  ("40532176", 8),
  ("05321746", 8),
  ("53217406", 6),
  ("65321704", 8),
  ("53217064", 8),
  ("32170654", 8),
  ("21706534", 6),
  ("42170635", 8),
  ("21706345", 8),
  ("17063425", 8),
  ("70634215", 6),
  ("57063412", 8),
  ("70634152", 8),
  ("06341572", 8),
  ("63415702", 6),
  ("26341507", 6),
  ("72634105", 8),
  ("26341075", 8),
  ("63410725", 8),
  ("34107265", 8),
  ("41072635", 6),
  ("54107236", 8),
  ("41072356", 8),
  ("10723546", 8),
  ("07235416", 8),
  ("72354106", 6)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 16 := by decide

theorem based10 : basedOnCheck (List.range 8) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("36274051", 8)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("67235401", 8)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("67235401", 8),
  ("72354061", 8),
  ("23540671", 8),
  ("35406721", 8),
  ("54067231", 6),
  ("15406732", 8),
  ("54067312", 8),
  ("40673152", 8),
  ("06731542", 6),
  ("20673145", 8),
  ("06731425", 8),
  ("67314205", 6),
  ("56731402", 8),
  ("67314052", 8),
  ("73140562", 8),
  ("31405672", 8),
  ("14056732", 8),
  ("40567312", 6),
  ("24056713", 8),
  ("40567123", 8),
  ("05671243", 8),
  ("56712403", 6),
  ("35671204", 8),
  ("56712034", 8),
  ("67120354", 8),
  ("71203564", 6),
  ("47120365", 8),
  ("71203645", 8),
  ("12036475", 8),
  ("20364715", 6),
  ("52036417", 6),
  ("75203614", 8)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 16 := by decide

theorem based11 : basedOnCheck (List.range 8) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("67235401", 8)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("52036174", 8)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("52036174", 8),
  ("20361754", 8),
  ("03617524", 8),
  ("36175204", 6),
  ("43617502", 8),
  ("36175042", 8),
  ("61750432", 8),
  ("17504362", 8),
  ("75043612", 6),
  ("27504316", 8),
  ("75043126", 8),
  ("50431276", 8),
  ("04312756", 8),
  ("43127506", 6),
  ("64312705", 8),
  ("43127065", 8),
  ("31270645", 8),
  ("12706435", 6),
  ("51270634", 8),
  ("12706354", 8),
  ("27063514", 8),
  ("70635124", 6),
  ("47063521", 8),
  ("70635241", 8),
  ("06352471", 8),
  ("63524701", 8),
  ("35247061", 6),
  ("13524760", 8),
  ("35247610", 8),
  ("52476130", 8),
  ("24761350", 6),
  ("02476153", 8)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 14 := by decide

theorem based12 : basedOnCheck (List.range 8) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("52036174", 8)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("24761503", 8)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("24761503", 8),
  ("47615023", 6),
  ("34761520", 8),
  ("47615230", 8),
  ("76152340", 8),
  ("61523470", 8),
  ("15234760", 6),
  ("01523467", 6),
  ("70152364", 8),
  ("01523674", 8),
  ("15236704", 8),
  ("52367014", 8),
  ("23670154", 8),
  ("36701524", 6),
  ("43670125", 8),
  ("36701245", 8),
  ("67012435", 8),
  ("70124365", 6),
  ("57012463", 8),
  ("70124653", 8),
  ("01246573", 8),
  ("12465703", 8),
  ("24657013", 6),
  ("32465710", 8),
  ("24657130", 8),
  ("46571320", 8),
  ("65713240", 6),
  ("06571342", 8),
  ("65713402", 8),
  ("57134062", 8),
  ("71340652", 6),
  ("27134056", 8)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 16 := by decide

theorem based13 : basedOnCheck (List.range 8) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("24761503", 8)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("71340526", 8)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("71340526", 8),
  ("13405276", 8),
  ("34052716", 8),
  ("40527136", 6),
  ("64052731", 8),
  ("40527361", 8),
  ("05273641", 6),
  ("10527346", 8),
  ("05273416", 8),
  ("52734106", 8),
  ("27341056", 6),
  ("62734150", 8),
  ("27341560", 8),
  ("73415620", 8),
  ("34156270", 8),
  ("41562730", 6),
  ("04156237", 6),
  ("70415632", 8),
  ("04156372", 8),
  ("41563702", 8),
  ("15637042", 8),
  ("56370412", 8),
  ("63704152", 6),
  ("26370451", 8),
  ("63704521", 8),
  ("37045261", 6),
  ("13704562", 8),
  ("37045612", 8),
  ("70456132", 8),
  ("04561372", 8),
  ("45613702", 6),
  ("24561307", 6)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 18 := by decide

theorem based14 : basedOnCheck (List.range 8) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("71340526", 8)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("72456103", 8)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("72456103", 8),
  ("24561073", 8),
  ("45610723", 8),
  ("56107243", 8),
  ("61072453", 6),
  ("36107254", 8),
  ("61072534", 8),
  ("10725364", 8),
  ("07253614", 8),
  ("72536104", 6),
  ("47253601", 8),
  ("72536041", 8),
  ("25360471", 8),
  ("53604721", 8),
  ("36047251", 6),
  ("13604752", 8),
  ("36047512", 8),
  ("60475132", 8),
  ("04751362", 6),
  ("20475163", 8),
  ("04751623", 8),
  ("47516203", 8),
  ("75162043", 6),
  ("37516240", 8),
  ("75162430", 8),
  ("51624370", 8),
  ("16243750", 8),
  ("62437510", 6),
  ("06243715", 8),
  ("62437105", 8),
  ("24371065", 8),
  ("43710625", 6)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 32 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 14 := by decide

theorem based15 : basedOnCheck (List.range 8) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("72456103", 8)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("54371026", 8)) = true := by rfl

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

theorem rows_charge : (rows.map Row.charge).sum = 246 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, charge08, charge09, charge10, charge11, charge12, charge13, charge14, charge15, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 8) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, based08, based09, based10, based11, based12, based13, based14, based15, Bool.and_self]

def suffix15 : List (Row Nat) := rows15

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("72456103", 8)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("54371026", 8)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("71340526", 8)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("24761503", 8)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("52036174", 8)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("67235401", 8)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("36274051", 8)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("62104753", 8)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("73142650", 8)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("24760531", 6)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("04537126", 6)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("37651024", 8)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("63471502", 6)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("74620153", 8)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("32750146", 6)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("41352076", 8)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("14276305", 8)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("54371026", 8)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("14276305", 8)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("54371026", 8)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.Halfar0Parts.C03
