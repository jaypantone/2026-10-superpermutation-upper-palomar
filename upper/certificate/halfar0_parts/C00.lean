module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original Halfar0 rows 0 through 511.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.Halfar0Parts.C00
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("70123456", 6),
  ("67012354", 8),
  ("70123564", 8),
  ("01235674", 8),
  ("12356704", 6),
  ("41235607", 6),
  ("74123506", 8),
  ("41235076", 8),
  ("12350746", 8),
  ("23507416", 8),
  ("35074126", 6),
  ("63507421", 8),
  ("35074261", 8),
  ("50742631", 8),
  ("07426351", 8),
  ("74263501", 6),
  ("17426305", 8),
  ("74263015", 8),
  ("42630175", 8),
  ("26301745", 8),
  ("63017425", 6),
  ("56301724", 8),
  ("63017254", 8),
  ("30172564", 8),
  ("01725634", 6),
  ("40172536", 8),
  ("01725346", 8),
  ("17253406", 8),
  ("72534016", 6),
  ("67253410", 8),
  ("72534160", 8),
  ("25341670", 8)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 16 := by decide

theorem based00 : basedOnCheck (List.range 8) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("70123456", 6)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("53416720", 8)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("53416720", 8),
  ("34167250", 6),
  ("03416752", 8),
  ("34167502", 8),
  ("41675032", 8),
  ("16750342", 6),
  ("21675043", 8),
  ("16750423", 8),
  ("67504213", 6),
  ("36750412", 8),
  ("67504132", 8),
  ("75041362", 8),
  ("50413672", 8),
  ("04136752", 6),
  ("20413657", 6),
  ("72041356", 8),
  ("20413576", 8),
  ("04135726", 8),
  ("41357206", 8),
  ("13572046", 8),
  ("35720416", 6),
  ("63572014", 8),
  ("35720164", 8),
  ("57201634", 8),
  ("72016354", 6),
  ("47201653", 8),
  ("72016543", 8),
  ("20165473", 8),
  ("01654723", 8),
  ("16547203", 6),
  ("31654702", 8),
  ("16547032", 8)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 16 := by decide

theorem based01 : basedOnCheck (List.range 8) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("53416720", 8)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("65470312", 6)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("65470312", 6),
  ("26547013", 8),
  ("65470123", 8),
  ("54701263", 8),
  ("47012653", 8),
  ("70126543", 6),
  ("37012645", 8),
  ("70126435", 8),
  ("01264375", 8),
  ("12643705", 8),
  ("26437015", 6),
  ("52643710", 8),
  ("26437150", 8),
  ("64371520", 8),
  ("43715260", 6),
  ("04371562", 8),
  ("43715602", 8),
  ("37156042", 6),
  ("23715640", 8),
  ("37156420", 8),
  ("71564230", 8),
  ("15642370", 8),
  ("56423710", 6),
  ("05642317", 6),
  ("70564213", 8),
  ("05642173", 8),
  ("56421703", 8),
  ("64217053", 8),
  ("42170563", 8),
  ("21705643", 6),
  ("32170546", 8),
  ("21705436", 8)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 16 := by decide

theorem based02 : basedOnCheck (List.range 8) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("65470312", 6)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("17054326", 8)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("17054326", 8),
  ("70543216", 6),
  ("67054312", 8),
  ("70543162", 8),
  ("05431672", 8),
  ("54316702", 8),
  ("43167052", 6),
  ("24316750", 8),
  ("43167520", 8),
  ("31675240", 8),
  ("16752430", 6),
  ("01675234", 8),
  ("16752304", 8),
  ("67523014", 8),
  ("75230164", 6),
  ("47523061", 8),
  ("75230641", 8),
  ("52306471", 8),
  ("23064751", 8),
  ("30647521", 6),
  ("13064725", 8),
  ("30647215", 8),
  ("06472135", 6),
  ("50647231", 8),
  ("06472351", 8),
  ("64723501", 8),
  ("47235061", 6),
  ("14723560", 8),
  ("47235610", 8),
  ("72356140", 8),
  ("23561470", 8),
  ("35614720", 8)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 14 := by decide

theorem based03 : basedOnCheck (List.range 8) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("17054326", 8)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("56147230", 6)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("56147230", 6),
  ("05614732", 8),
  ("56147302", 8),
  ("61473052", 8),
  ("14730562", 6),
  ("21473065", 8),
  ("14730625", 8),
  ("47306215", 6),
  ("54730612", 8),
  ("47306152", 8),
  ("73061542", 8),
  ("30615472", 8),
  ("06154732", 8),
  ("61547302", 6),
  ("26154703", 8),
  ("61547023", 8),
  ("15470263", 8),
  ("54702613", 6),
  ("35470216", 8),
  ("54702136", 8),
  ("47021356", 6),
  ("64702153", 8),
  ("47021563", 8),
  ("70215643", 8),
  ("02156473", 8),
  ("21564703", 6),
  ("32156407", 6),
  ("73215604", 8),
  ("32156074", 8),
  ("21560734", 8),
  ("15607324", 8),
  ("56073214", 8)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 16 := by decide

theorem based04 : basedOnCheck (List.range 8) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("56147230", 6)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("60732154", 6)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("60732154", 6),
  ("46073251", 8),
  ("60732541", 8),
  ("07325461", 8),
  ("73254601", 6),
  ("17325406", 8),
  ("73254016", 8),
  ("32540176", 8),
  ("25401736", 8),
  ("54017326", 6),
  ("65401723", 8),
  ("54017263", 8),
  ("40172653", 8),
  ("01726543", 6),
  ("30172645", 8),
  ("01726435", 8),
  ("17264305", 8),
  ("72643015", 6),
  ("57264310", 8),
  ("72643150", 8),
  ("26431570", 8),
  ("64315720", 8),
  ("43157260", 6),
  ("04315762", 8),
  ("43157602", 8),
  ("31576042", 6),
  ("23157640", 8),
  ("31576420", 8),
  ("15764230", 8),
  ("57642310", 6),
  ("05764213", 8),
  ("57642103", 8)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 16 := by decide

theorem based05 : basedOnCheck (List.range 8) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("60732154", 6)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("76421053", 8)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("76421053", 8),
  ("64210573", 8),
  ("42105763", 8),
  ("21057643", 6),
  ("32105746", 8),
  ("21057436", 8),
  ("10574326", 8),
  ("05743216", 6),
  ("60574312", 8),
  ("05743162", 8),
  ("57431602", 8),
  ("74316052", 6),
  ("27431650", 8),
  ("74316520", 8),
  ("43165270", 8),
  ("31652740", 8),
  ("16527430", 6),
  ("01652734", 8),
  ("16527304", 8),
  ("65273014", 8),
  ("52730164", 6),
  ("45273061", 8),
  ("52730641", 8),
  ("27306451", 8),
  ("73064521", 6),
  ("17306425", 8),
  ("73064215", 8),
  ("30642175", 8),
  ("06421735", 6),
  ("50642137", 6),
  ("75064231", 8),
  ("50642371", 8)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 16 := by decide

theorem based06 : basedOnCheck (List.range 8) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("76421053", 8)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("06423751", 8)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("06423751", 8),
  ("64237501", 8),
  ("42375061", 6),
  ("14237560", 8),
  ("42375610", 8),
  ("23756140", 8),
  ("37561420", 8),
  ("75614230", 6),
  ("07561432", 8),
  ("75614302", 8),
  ("56143072", 8),
  ("61430752", 8),
  ("14307562", 6),
  ("21430765", 8),
  ("14307625", 8),
  ("43076215", 6),
  ("54307612", 8),
  ("43076152", 8),
  ("30761542", 8),
  ("07615432", 8),
  ("76154302", 6),
  ("27615403", 8),
  ("76154023", 8),
  ("61540273", 8),
  ("15402763", 8),
  ("54027613", 6),
  ("35402716", 8),
  ("54027136", 8),
  ("40271356", 6),
  ("64027153", 8),
  ("40271563", 8),
  ("02715643", 8)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 14 := by decide

theorem based07 : basedOnCheck (List.range 8) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("06423751", 8)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("27156403", 6)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("27156403", 6),
  ("32715604", 8),
  ("27156034", 8),
  ("71560324", 8),
  ("15603274", 8),
  ("56032714", 8),
  ("60327154", 6),
  ("46032751", 8),
  ("60327541", 8),
  ("03275461", 8),
  ("32754601", 6),
  ("13275406", 8),
  ("32754016", 8),
  ("27540136", 8),
  ("75401326", 6),
  ("67540123", 8),
  ("75401263", 8),
  ("54012673", 8),
  ("40126753", 8),
  ("01267543", 6),
  ("30126745", 8),
  ("01267435", 8),
  ("12674305", 8),
  ("26743015", 6),
  ("52674310", 8),
  ("26743150", 8),
  ("67431520", 8),
  ("74315260", 6),
  ("07431562", 8),
  ("74315602", 8),
  ("43156072", 8),
  ("31560742", 6)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 16 := by decide

theorem based08 : basedOnCheck (List.range 8) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("27156403", 6)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("23156047", 6)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("23156047", 6),
  ("72315640", 8),
  ("23156470", 8),
  ("31564720", 8),
  ("15647230", 8),
  ("56472310", 6),
  ("05647213", 8),
  ("56472103", 8),
  ("64721053", 8),
  ("47210563", 8),
  ("72105643", 6),
  ("37210546", 8),
  ("72105436", 8),
  ("21054376", 8),
  ("10543726", 8),
  ("05437216", 6),
  ("60543712", 8),
  ("05437162", 8),
  ("54371602", 8),
  ("43716052", 6),
  ("24371650", 8),
  ("43716520", 8),
  ("37165240", 8),
  ("71652430", 6),
  ("07165234", 8),
  ("71652304", 8),
  ("16523074", 8),
  ("65230714", 8),
  ("52307164", 6),
  ("45230761", 8),
  ("52307641", 8),
  ("23076451", 8)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 14 := by decide

theorem based09 : basedOnCheck (List.range 8) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("23156047", 6)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("30764521", 6)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("30764521", 6),
  ("13076425", 8),
  ("30764215", 8),
  ("07642135", 6),
  ("50764231", 8),
  ("07642351", 8),
  ("76423501", 8),
  ("64235071", 8),
  ("42350761", 6),
  ("14235067", 6),
  ("71423560", 8),
  ("14235670", 8),
  ("42356710", 8),
  ("23567140", 8),
  ("35671420", 8),
  ("56714230", 6),
  ("05671432", 8),
  ("56714302", 8),
  ("67143052", 8),
  ("71430562", 6),
  ("27143065", 8),
  ("71430625", 8),
  ("14306275", 8),
  ("43062715", 6),
  ("54306217", 6),
  ("75430612", 8),
  ("54306172", 8),
  ("43061752", 8),
  ("30617542", 8),
  ("06175432", 8),
  ("61754302", 6),
  ("26175403", 8)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 18 := by decide

theorem based10 : basedOnCheck (List.range 8) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("30764521", 6)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("61754023", 8)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("61754023", 8),
  ("17540263", 8),
  ("75402613", 6),
  ("37540216", 8),
  ("75402136", 8),
  ("54021376", 8),
  ("40213756", 6),
  ("64021357", 6),
  ("76402153", 8),
  ("64021573", 8),
  ("40215763", 8),
  ("02157643", 8),
  ("21576403", 6),
  ("32157604", 8),
  ("21576034", 8),
  ("15760324", 8),
  ("57603214", 8),
  ("76032154", 6),
  ("47603251", 8),
  ("76032541", 8),
  ("60325471", 8),
  ("03254761", 8),
  ("32547601", 6),
  ("13254706", 8),
  ("32547016", 8),
  ("25470136", 6),
  ("62547031", 8),
  ("25470361", 8),
  ("54703621", 8),
  ("47036251", 6),
  ("14703652", 8),
  ("47036512", 8)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 16 := by decide

theorem based11 : basedOnCheck (List.range 8) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("61754023", 8)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("70365142", 8)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("70365142", 8),
  ("03651472", 8),
  ("36514702", 8),
  ("65147032", 6),
  ("26514730", 8),
  ("65147320", 8),
  ("51473260", 8),
  ("14732650", 6),
  ("01473256", 8),
  ("14732506", 8),
  ("47325016", 8),
  ("73250146", 6),
  ("67325041", 8),
  ("73250461", 8),
  ("32504671", 8),
  ("25046731", 8),
  ("50467321", 6),
  ("15046723", 8),
  ("50467213", 8),
  ("04672153", 8),
  ("46721503", 6),
  ("34672105", 8),
  ("46721035", 8),
  ("67210345", 6),
  ("56721043", 8),
  ("67210453", 8),
  ("72104563", 8),
  ("21045673", 8),
  ("10456723", 6),
  ("31045627", 6),
  ("73104526", 8),
  ("31045276", 8)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 16 := by decide

theorem based12 : basedOnCheck (List.range 8) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("70365142", 8)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("10452736", 8)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("10452736", 8),
  ("04527316", 8),
  ("45273106", 8),
  ("52731046", 6),
  ("65273140", 8),
  ("52731460", 8),
  ("27314650", 8),
  ("73146520", 6),
  ("07314625", 8),
  ("73146205", 8),
  ("31462075", 8),
  ("14620735", 8),
  ("46207315", 6),
  ("54620713", 8),
  ("46207153", 8),
  ("62071543", 8),
  ("20715463", 6),
  ("32071564", 8),
  ("20715634", 8),
  ("07156324", 6),
  ("40715623", 8),
  ("07156243", 8),
  ("71562403", 8),
  ("15624073", 8),
  ("56240713", 8),
  ("62407153", 6),
  ("36240751", 8),
  ("62407531", 8),
  ("24075361", 8),
  ("40753621", 6),
  ("14075326", 8),
  ("40753216", 8)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 14 := by decide

theorem based13 : basedOnCheck (List.range 8) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("10452736", 8)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("07532146", 8)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("07532146", 8),
  ("75321406", 6),
  ("67532104", 8),
  ("75321064", 8),
  ("53210674", 8),
  ("32106754", 8),
  ("21067534", 6),
  ("42106735", 8),
  ("21067345", 8),
  ("10673425", 8),
  ("06734215", 6),
  ("50673412", 8),
  ("06734152", 8),
  ("67341502", 6),
  ("26734105", 8),
  ("67341025", 8),
  ("73410265", 8),
  ("34102675", 8),
  ("41026735", 6),
  ("54102637", 6),
  ("75410236", 8),
  ("54102376", 8),
  ("41023756", 8),
  ("10237546", 8),
  ("02375416", 8),
  ("23754106", 6),
  ("62375401", 8),
  ("23754061", 8),
  ("37540621", 8),
  ("75406231", 6),
  ("17540632", 8),
  ("75406312", 8)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 16 := by decide

theorem based14 : basedOnCheck (List.range 8) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("07532146", 8)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("54063172", 8)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("54063172", 8),
  ("40631752", 8),
  ("06317542", 6),
  ("20631745", 8),
  ("06317425", 8),
  ("63174205", 8),
  ("31742065", 6),
  ("53174260", 8),
  ("31742650", 8),
  ("17426530", 8),
  ("74265310", 6),
  ("07426513", 8),
  ("74265103", 8),
  ("42651073", 8),
  ("26510743", 8),
  ("65107423", 6),
  ("36510724", 8),
  ("65107234", 8),
  ("51072364", 6),
  ("45107263", 8),
  ("51072643", 8),
  ("10726453", 8),
  ("07264513", 6),
  ("30726415", 8),
  ("07264135", 8),
  ("72641305", 8),
  ("26413075", 8),
  ("64130725", 8),
  ("41307265", 6),
  ("54130762", 8),
  ("41307652", 8),
  ("13076542", 8)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 32 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 14 := by decide

theorem based15 : basedOnCheck (List.range 8) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("54063172", 8)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("30765412", 6)) = true := by rfl

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

theorem rows_charge : (rows.map Row.charge).sum = 248 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, charge08, charge09, charge10, charge11, charge12, charge13, charge14, charge15, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 8) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, based08, based09, based10, based11, based12, based13, based14, based15, Bool.and_self]

def suffix15 : List (Row Nat) := rows15

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("54063172", 8)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("30765412", 6)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("07532146", 8)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("10452736", 8)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("70365142", 8)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("61754023", 8)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("30764521", 6)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("23156047", 6)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("27156403", 6)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("06423751", 8)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("76421053", 8)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("60732154", 6)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("56147230", 6)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("17054326", 8)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("65470312", 6)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("53416720", 8)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("70123456", 6)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("30765412", 6)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("70123456", 6)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("30765412", 6)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.Halfar0Parts.C00
