module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original Halfar1 rows 1536 through 2047.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.Halfar1Parts.C03
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("51436072", 8),
  ("14360752", 8),
  ("43607512", 8),
  ("36075142", 6),
  ("23607541", 8),
  ("36075421", 8),
  ("60754231", 8),
  ("07542361", 6),
  ("10754263", 8),
  ("07542613", 8),
  ("75426103", 6),
  ("37542601", 8),
  ("75426031", 8),
  ("54260371", 8),
  ("42603751", 8),
  ("26037541", 6),
  ("12603745", 8),
  ("26037415", 8),
  ("60374125", 8),
  ("03741265", 8),
  ("37412605", 6),
  ("53741206", 8),
  ("37412056", 8),
  ("74120536", 8),
  ("41205376", 8),
  ("12053746", 6),
  ("61205347", 6),
  ("76120543", 8),
  ("61205473", 8),
  ("12054763", 8),
  ("20547613", 8),
  ("05476123", 6)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 16 := by decide

theorem based00 : basedOnCheck (List.range 8) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("51436072", 8)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("30547621", 8)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("30547621", 8),
  ("05476231", 8),
  ("54762301", 8),
  ("47623051", 6),
  ("14762350", 8),
  ("47623510", 8),
  ("76235140", 8),
  ("62351470", 8),
  ("23514760", 6),
  ("02351467", 6),
  ("70235164", 8),
  ("02351674", 8),
  ("23516704", 8),
  ("35167024", 8),
  ("51670234", 6),
  ("45167032", 8),
  ("51670342", 8),
  ("16703452", 6),
  ("21670354", 8),
  ("16703524", 8),
  ("67035214", 8),
  ("70352164", 6),
  ("47035261", 8),
  ("70352641", 8),
  ("03526471", 8),
  ("35264701", 8),
  ("52647031", 8),
  ("26470351", 6),
  ("12647053", 8),
  ("26470513", 8),
  ("64705123", 8),
  ("47051263", 6)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 16 := by decide

theorem based01 : basedOnCheck (List.range 8) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("30547621", 8)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("34705162", 8)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("34705162", 8),
  ("47051632", 8),
  ("70516342", 8),
  ("05163472", 8),
  ("51634702", 6),
  ("25163407", 6),
  ("72516304", 8),
  ("25163074", 8),
  ("51630724", 8),
  ("16307254", 8),
  ("63072514", 6),
  ("46307215", 8),
  ("63072145", 8),
  ("30721465", 8),
  ("07214635", 6),
  ("50721436", 8),
  ("07214356", 8),
  ("72143506", 8),
  ("21435076", 8),
  ("14350726", 6),
  ("61435027", 6),
  ("76143520", 8),
  ("61435270", 8),
  ("14352760", 8),
  ("43527610", 6),
  ("04352716", 8),
  ("43527106", 8),
  ("35271046", 8),
  ("52710436", 6),
  ("65271034", 8),
  ("52710364", 8),
  ("27103654", 8)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 16 := by decide

theorem based02 : basedOnCheck (List.range 8) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("34705162", 8)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("71036524", 6)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("71036524", 6),
  ("47103625", 8),
  ("71036245", 8),
  ("10362475", 8),
  ("03624715", 8),
  ("36247105", 8),
  ("62471035", 6),
  ("56247130", 8),
  ("62471350", 8),
  ("24713560", 6),
  ("02471365", 8),
  ("24713605", 8),
  ("47136025", 8),
  ("71360245", 8),
  ("13602475", 8),
  ("36024715", 6),
  ("53602417", 6),
  ("75360214", 8),
  ("53602174", 8),
  ("36021754", 8),
  ("60217534", 6),
  ("46021735", 8),
  ("60217345", 8),
  ("02173465", 8),
  ("21734605", 8),
  ("17346025", 6),
  ("51734620", 8),
  ("17346250", 8),
  ("73462510", 8),
  ("34625170", 8),
  ("46251730", 6),
  ("04625137", 6)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 18 := by decide

theorem based03 : basedOnCheck (List.range 8) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("71036524", 6)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("70462531", 8)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("70462531", 8),
  ("04625371", 8),
  ("46253701", 8),
  ("62537041", 8),
  ("25370461", 6),
  ("12537064", 8),
  ("25370614", 8),
  ("53706124", 6),
  ("45370621", 8),
  ("53706241", 8),
  ("37062451", 8),
  ("70624531", 8),
  ("06245371", 8),
  ("62453701", 6),
  ("16245307", 6),
  ("71624503", 8),
  ("16245073", 8),
  ("62450713", 8),
  ("24507163", 8),
  ("45071623", 6),
  ("34507126", 8),
  ("45071236", 8),
  ("50712346", 8),
  ("07123456", 6),
  ("60712354", 8),
  ("07123564", 8),
  ("71235604", 6),
  ("47123506", 8),
  ("71235046", 8),
  ("12350476", 8),
  ("23504716", 8),
  ("35047126", 6)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 16 := by decide

theorem based04 : basedOnCheck (List.range 8) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("70462531", 8)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("63504721", 8)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("63504721", 8),
  ("35047261", 8),
  ("50472631", 8),
  ("04726351", 8),
  ("47263501", 6),
  ("14726305", 8),
  ("47263015", 8),
  ("72630145", 8),
  ("26301475", 8),
  ("63014725", 6),
  ("56301427", 6),
  ("75630124", 8),
  ("56301274", 8),
  ("63012754", 8),
  ("30127564", 8),
  ("01275634", 6),
  ("40127536", 8),
  ("01275346", 8),
  ("12753406", 8),
  ("27534016", 6),
  ("62753410", 8),
  ("27534160", 8),
  ("75341620", 8),
  ("53416270", 8),
  ("34162750", 6),
  ("03416257", 6),
  ("70341652", 8),
  ("03416572", 8),
  ("34165702", 8),
  ("41657032", 8),
  ("16570342", 6),
  ("21657043", 8)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 16 := by decide

theorem based05 : basedOnCheck (List.range 8) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("63504721", 8)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("16570423", 8)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("16570423", 8),
  ("65704213", 6),
  ("36570412", 8),
  ("65704132", 8),
  ("57041362", 8),
  ("70413652", 6),
  ("27041356", 8),
  ("70413526", 8),
  ("04135276", 8),
  ("41352706", 8),
  ("13527046", 8),
  ("35270416", 6),
  ("63527014", 8),
  ("35270164", 8),
  ("52701634", 8),
  ("27016354", 6),
  ("42701653", 8),
  ("27016543", 8),
  ("70165423", 8),
  ("01654273", 8),
  ("16542703", 6),
  ("31654207", 6),
  ("73165402", 8),
  ("31654072", 8),
  ("16540732", 8),
  ("65407312", 8),
  ("54073162", 6),
  ("25407361", 8),
  ("54073621", 8),
  ("40736251", 6),
  ("14073652", 8),
  ("40736512", 8)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 16 := by decide

theorem based06 : basedOnCheck (List.range 8) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("16570423", 8)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("07365142", 8)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("07365142", 8),
  ("73651402", 8),
  ("36514072", 8),
  ("65140732", 6),
  ("26514037", 6),
  ("72651430", 8),
  ("26514370", 8),
  ("65143720", 8),
  ("51437260", 8),
  ("14372650", 6),
  ("01437256", 8),
  ("14372506", 8),
  ("43725016", 8),
  ("37250146", 6),
  ("63725041", 8),
  ("37250461", 8),
  ("72504631", 8),
  ("25046371", 8),
  ("50463721", 6),
  ("15046327", 6),
  ("71504623", 8),
  ("15046273", 8),
  ("50462713", 8),
  ("04627153", 8),
  ("46271503", 6),
  ("34627105", 8),
  ("46271035", 8),
  ("62710345", 6),
  ("56271043", 8),
  ("62710453", 8),
  ("27104563", 8),
  ("71045623", 6)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 18 := by decide

theorem based07 : basedOnCheck (List.range 8) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("07365142", 8)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("37104526", 8)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("37104526", 8),
  ("71045236", 8),
  ("10452376", 8),
  ("04523716", 8),
  ("45237106", 8),
  ("52371046", 6),
  ("65237140", 8),
  ("52371460", 8),
  ("23714650", 8),
  ("37146520", 6),
  ("03714625", 8),
  ("37146205", 8),
  ("71462035", 8),
  ("14620375", 8),
  ("46203715", 6),
  ("54620317", 6),
  ("75462013", 8),
  ("54620173", 8),
  ("46201753", 8),
  ("62017543", 8),
  ("20175463", 6),
  ("32017564", 8),
  ("20175634", 8),
  ("01756324", 6),
  ("40175623", 8),
  ("01756243", 8),
  ("17562403", 8),
  ("75624013", 8),
  ("56240173", 8),
  ("62401753", 6),
  ("36240157", 6),
  ("73624051", 8)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 16 := by decide

theorem based08 : basedOnCheck (List.range 8) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("37104526", 8)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("36240571", 8)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("36240571", 8),
  ("62405731", 8),
  ("24057361", 8),
  ("40573621", 6),
  ("14057326", 8),
  ("40573216", 8),
  ("05732146", 8),
  ("57321406", 6),
  ("65732104", 8),
  ("57321064", 8),
  ("73210654", 8),
  ("32106574", 8),
  ("21065734", 6),
  ("42106537", 6),
  ("74210635", 8),
  ("42106375", 8),
  ("21063745", 8),
  ("10637425", 8),
  ("06374215", 6),
  ("50637412", 8),
  ("06374152", 8),
  ("63741502", 6),
  ("26374105", 8),
  ("63741025", 8),
  ("37410265", 8),
  ("74102635", 6),
  ("57410236", 8),
  ("74102356", 8),
  ("41023576", 8),
  ("10235746", 8),
  ("02357416", 8),
  ("23574106", 6)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 16 := by decide

theorem based09 : basedOnCheck (List.range 8) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("36240571", 8)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("62357401", 8)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("62357401", 8),
  ("23574061", 8),
  ("35740621", 8),
  ("57406231", 6),
  ("15740632", 8),
  ("57406312", 8),
  ("74063152", 8),
  ("40631572", 8),
  ("06315742", 6),
  ("20631547", 6),
  ("72063145", 8),
  ("20631475", 8),
  ("06314725", 8),
  ("63147205", 8),
  ("31472065", 6),
  ("53147260", 8),
  ("31472650", 8),
  ("14726530", 8),
  ("47265310", 6),
  ("04726513", 8),
  ("47265103", 8),
  ("72651043", 8),
  ("26510473", 8),
  ("65104723", 6),
  ("36510427", 6),
  ("73651024", 8),
  ("36510274", 8),
  ("65102734", 8),
  ("51027364", 6),
  ("45102763", 8),
  ("51027643", 8),
  ("10276453", 8)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 16 := by decide

theorem based10 : basedOnCheck (List.range 8) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("62357401", 8)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("02764513", 6)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("02764513", 6),
  ("30276415", 8),
  ("02764135", 8),
  ("27641305", 8),
  ("76413025", 8),
  ("64130275", 8),
  ("41302765", 6),
  ("54130267", 6),
  ("75413062", 8),
  ("54130672", 8),
  ("41306752", 8),
  ("13067542", 8),
  ("30675412", 6),
  ("23067514", 8),
  ("30675124", 8),
  ("06751234", 8),
  ("67512304", 6),
  ("46751203", 8),
  ("67512043", 8),
  ("75120463", 8),
  ("51204673", 8),
  ("12046753", 6),
  ("31204657", 6),
  ("73120456", 8),
  ("31204576", 8),
  ("12045736", 8),
  ("20457316", 8),
  ("04573126", 6),
  ("60457321", 8),
  ("04573261", 8),
  ("45732601", 8),
  ("57326041", 6)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 18 := by decide

theorem based11 : basedOnCheck (List.range 8) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("02764513", 6)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("15732640", 8)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("15732640", 8),
  ("57326410", 8),
  ("73264150", 6),
  ("07326451", 8),
  ("73264501", 8),
  ("32645071", 8),
  ("26450731", 8),
  ("64507321", 6),
  ("16450723", 8),
  ("64507213", 8),
  ("45072163", 8),
  ("50721643", 8),
  ("07216453", 6),
  ("30721654", 8),
  ("07216534", 8),
  ("72165304", 8),
  ("21653074", 8),
  ("16530724", 6),
  ("41653027", 6),
  ("74165320", 8),
  ("41653270", 8),
  ("16532740", 8),
  ("65327410", 8),
  ("53274160", 6),
  ("05327461", 8),
  ("53274601", 8),
  ("32746051", 8),
  ("27460531", 6),
  ("12746035", 8),
  ("27460315", 8),
  ("74603125", 8),
  ("46031275", 8)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 14 := by decide

theorem based12 : basedOnCheck (List.range 8) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("15732640", 8)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("60312745", 6)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("60312745", 6),
  ("56031247", 6),
  ("75603142", 8),
  ("56031472", 8),
  ("60314752", 8),
  ("03147562", 8),
  ("31475602", 6),
  ("23147506", 8),
  ("31475026", 8),
  ("14750236", 6),
  ("61475032", 8),
  ("14750362", 8),
  ("47503612", 8),
  ("75036142", 6),
  ("27503641", 8),
  ("75036421", 8),
  ("50364271", 8),
  ("03642751", 8),
  ("36427501", 8),
  ("64275031", 6),
  ("16427530", 8),
  ("64275310", 8),
  ("42753160", 8),
  ("27531640", 6),
  ("02753146", 8),
  ("27531406", 8),
  ("75314026", 8),
  ("53140276", 8),
  ("31402756", 6),
  ("63140257", 6),
  ("76314052", 8),
  ("63140572", 8)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 18 := by decide

theorem based13 : basedOnCheck (List.range 8) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("60312745", 6)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("31405762", 8)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("31405762", 8),
  ("14057632", 8),
  ("40576312", 6),
  ("24057613", 8),
  ("40576123", 8),
  ("05761243", 8),
  ("57612403", 6),
  ("35761204", 8),
  ("57612034", 8),
  ("76120354", 8),
  ("61203574", 8),
  ("12035764", 6),
  ("41203567", 6),
  ("74120365", 8),
  ("41203675", 8),
  ("12036745", 8),
  ("20367415", 6),
  ("52036714", 8),
  ("20367154", 8),
  ("03671524", 8),
  ("36715204", 6),
  ("43671502", 8),
  ("36715042", 8),
  ("67150432", 8),
  ("71504362", 8),
  ("15043672", 8),
  ("50436712", 6),
  ("25043617", 6),
  ("72504316", 8),
  ("25043176", 8),
  ("50431726", 8),
  ("04317256", 8)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 16 := by decide

theorem based14 : basedOnCheck (List.range 8) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("31405762", 8)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("43172506", 6)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("43172506", 6),
  ("64317205", 8),
  ("43172065", 8),
  ("31720645", 8),
  ("17206435", 6),
  ("51720634", 8),
  ("17206354", 8),
  ("72063514", 8),
  ("20635174", 8),
  ("06351724", 6),
  ("40635127", 6),
  ("74063521", 8),
  ("40635271", 8),
  ("06352741", 8),
  ("63527401", 8),
  ("35274061", 6),
  ("13527460", 8),
  ("35274610", 8),
  ("52746130", 8),
  ("27461350", 6),
  ("02746153", 8),
  ("27461503", 8),
  ("74615023", 6),
  ("37461520", 8),
  ("74615230", 8),
  ("46152370", 8),
  ("61523740", 8),
  ("15237460", 6),
  ("01523764", 8),
  ("15237604", 8),
  ("52376014", 8),
  ("23760154", 8)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 32 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 16 := by decide

theorem based15 : basedOnCheck (List.range 8) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("43172506", 6)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("37601524", 6)) = true := by rfl

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

theorem rows_charge : (rows.map Row.charge).sum = 262 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, charge08, charge09, charge10, charge11, charge12, charge13, charge14, charge15, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 8) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, based08, based09, based10, based11, based12, based13, based14, based15, Bool.and_self]

def suffix15 : List (Row Nat) := rows15

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("43172506", 6)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("37601524", 6)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("31405762", 8)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("60312745", 6)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("15732640", 8)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("02764513", 6)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("62357401", 8)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("36240571", 8)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("37104526", 8)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("07365142", 8)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("16570423", 8)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("63504721", 8)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("70462531", 8)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("71036524", 6)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("34705162", 8)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("30547621", 8)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("51436072", 8)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("37601524", 6)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("51436072", 8)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("37601524", 6)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.Halfar1Parts.C03
