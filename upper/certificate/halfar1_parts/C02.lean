module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original Halfar1 rows 1024 through 1535.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.Halfar1Parts.C02
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("70642135", 6),
  ("57064231", 8),
  ("70642351", 8),
  ("06423571", 8),
  ("64235701", 8),
  ("42357061", 6),
  ("14235760", 8),
  ("42357610", 8),
  ("23576140", 8),
  ("35761420", 8),
  ("57614230", 6),
  ("05761432", 8),
  ("57614302", 8),
  ("76143052", 8),
  ("61430572", 8),
  ("14305762", 6),
  ("21430567", 6),
  ("72143065", 8),
  ("21430675", 8),
  ("14306725", 8),
  ("43067215", 6),
  ("54306712", 8),
  ("43067152", 8),
  ("30671542", 8),
  ("06715432", 6),
  ("20671534", 8),
  ("06715324", 8),
  ("67153204", 8),
  ("71532064", 8),
  ("15320674", 8),
  ("53206714", 6),
  ("45320617", 6)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 18 := by decide

theorem based00 : basedOnCheck (List.range 8) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("70642135", 6)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("74532016", 8)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("74532016", 8),
  ("45320176", 8),
  ("53201746", 8),
  ("32017456", 8),
  ("20174536", 6),
  ("62017435", 8),
  ("20174365", 8),
  ("01743625", 8),
  ("17436205", 6),
  ("51743602", 8),
  ("17436052", 8),
  ("74360512", 8),
  ("43605172", 8),
  ("36051742", 6),
  ("23605147", 6),
  ("72360541", 8),
  ("23605471", 8),
  ("36054721", 8),
  ("60547231", 8),
  ("05472361", 6),
  ("10547263", 8),
  ("05472613", 8),
  ("54726103", 6),
  ("35472601", 8),
  ("54726031", 8),
  ("47260351", 8),
  ("72603541", 6),
  ("17260345", 8),
  ("72603415", 8),
  ("26034175", 8),
  ("60341725", 8),
  ("03417265", 8)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 14 := by decide

theorem based01 : basedOnCheck (List.range 8) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("74532016", 8)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("34172605", 6)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("34172605", 6),
  ("53417206", 8),
  ("34172056", 8),
  ("41720536", 8),
  ("17205346", 6),
  ("61720543", 8),
  ("17205463", 8),
  ("72054613", 8),
  ("20546173", 8),
  ("05461723", 6),
  ("30546127", 6),
  ("73054621", 8),
  ("30546271", 8),
  ("05462731", 8),
  ("54627301", 8),
  ("46273051", 6),
  ("14627350", 8),
  ("46273510", 8),
  ("62735140", 8),
  ("27351460", 6),
  ("02735164", 8),
  ("27351604", 8),
  ("73516024", 8),
  ("35160274", 8),
  ("51602734", 6),
  ("45160237", 6),
  ("74516032", 8),
  ("45160372", 8),
  ("51603742", 8),
  ("16037452", 6),
  ("21603754", 8),
  ("16037524", 8)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 18 := by decide

theorem based02 : basedOnCheck (List.range 8) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("34172605", 6)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("60375214", 8)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("60375214", 8),
  ("03752164", 6),
  ("40375261", 8),
  ("03752641", 8),
  ("37526401", 8),
  ("75264031", 8),
  ("52640371", 8),
  ("26403751", 6),
  ("12640357", 6),
  ("71264053", 8),
  ("12640573", 8),
  ("26405713", 8),
  ("64057123", 8),
  ("40571263", 6),
  ("34057162", 8),
  ("40571632", 8),
  ("05716342", 8),
  ("57163402", 6),
  ("25716304", 8),
  ("57163024", 8),
  ("71630254", 8),
  ("16302574", 8),
  ("63025714", 6),
  ("46302517", 6),
  ("74630215", 8),
  ("46302175", 8),
  ("63021745", 8),
  ("30217465", 8),
  ("02174635", 6),
  ("50217436", 8),
  ("02174356", 8),
  ("21743506", 8)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 16 := by decide

theorem based03 : basedOnCheck (List.range 8) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("60375214", 8)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("17435026", 6)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("17435026", 6),
  ("61743520", 8),
  ("17435260", 8),
  ("74352610", 6),
  ("07435216", 8),
  ("74352106", 8),
  ("43521076", 8),
  ("35210746", 8),
  ("52107436", 6),
  ("65210734", 8),
  ("52107364", 8),
  ("21073654", 8),
  ("10736524", 6),
  ("41073625", 8),
  ("10736245", 8),
  ("07362415", 8),
  ("73624105", 8),
  ("36241075", 8),
  ("62410735", 6),
  ("56241037", 6),
  ("75624130", 8),
  ("56241370", 8),
  ("62413750", 8),
  ("24137560", 6),
  ("02413765", 8),
  ("24137605", 8),
  ("41376025", 8),
  ("13760245", 8),
  ("37602415", 6),
  ("53760214", 8),
  ("37602154", 8),
  ("76021534", 6)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 18 := by decide

theorem based04 : basedOnCheck (List.range 8) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("17435026", 6)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("47602135", 8)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("47602135", 8),
  ("76021345", 8),
  ("60213475", 8),
  ("02134765", 8),
  ("21347605", 8),
  ("13476025", 6),
  ("51347620", 8),
  ("13476250", 8),
  ("34762510", 8),
  ("47625130", 6),
  ("04762531", 8),
  ("47625301", 8),
  ("76253041", 8),
  ("62530471", 8),
  ("25304761", 6),
  ("12530467", 6),
  ("71253064", 8),
  ("12530674", 8),
  ("25306714", 8),
  ("53067124", 6),
  ("45306721", 8),
  ("53067241", 8),
  ("30672451", 8),
  ("06724531", 8),
  ("67245301", 6),
  ("16724503", 8),
  ("67245013", 8),
  ("72450163", 8),
  ("24501673", 8),
  ("45016723", 6),
  ("34501627", 6),
  ("73450126", 8)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 16 := by decide

theorem based05 : basedOnCheck (List.range 8) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("47602135", 8)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("34501276", 8)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("34501276", 8),
  ("45012736", 8),
  ("50127346", 8),
  ("01273456", 6),
  ("60127354", 8),
  ("01273564", 8),
  ("12735604", 6),
  ("41273506", 8),
  ("12735046", 8),
  ("27350416", 8),
  ("73504126", 6),
  ("67350421", 8),
  ("73504261", 8),
  ("35042671", 8),
  ("50426731", 8),
  ("04267351", 8),
  ("42673501", 6),
  ("14267305", 8),
  ("42673015", 8),
  ("26730145", 8),
  ("67301425", 6),
  ("56730124", 8),
  ("67301254", 8),
  ("73012564", 8),
  ("30125674", 8),
  ("01256734", 6),
  ("40125637", 6),
  ("74012536", 8),
  ("40125376", 8),
  ("01253746", 8),
  ("12537406", 8),
  ("25374016", 6)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 16 := by decide

theorem based06 : basedOnCheck (List.range 8) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("34501276", 8)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("62537410", 8)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("62537410", 8),
  ("25374160", 8),
  ("53741620", 8),
  ("37416250", 6),
  ("03741652", 8),
  ("37416502", 8),
  ("74165032", 8),
  ("41650372", 8),
  ("16503742", 6),
  ("21650347", 6),
  ("72165043", 8),
  ("21650473", 8),
  ("16504723", 8),
  ("65047213", 6),
  ("36504712", 8),
  ("65047132", 8),
  ("50471362", 8),
  ("04713652", 6),
  ("20471356", 8),
  ("04713526", 8),
  ("47135206", 8),
  ("71352046", 8),
  ("13520476", 8),
  ("35204716", 6),
  ("63520417", 6),
  ("76352014", 8),
  ("63520174", 8),
  ("35201764", 8),
  ("52017634", 8),
  ("20176354", 6),
  ("42017653", 8),
  ("20176543", 8)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 16 := by decide

theorem based07 : basedOnCheck (List.range 8) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("62537410", 8)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("01765423", 8)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("01765423", 8),
  ("17654203", 6),
  ("31765402", 8),
  ("17654032", 8),
  ("76540312", 8),
  ("65403172", 8),
  ("54031762", 6),
  ("25403167", 6),
  ("72540361", 8),
  ("25403671", 8),
  ("54036721", 8),
  ("40367251", 6),
  ("14036752", 8),
  ("40367512", 8),
  ("03675142", 8),
  ("36751402", 8),
  ("67514032", 6),
  ("26751430", 8),
  ("67514320", 8),
  ("75143260", 8),
  ("51432670", 8),
  ("14326750", 6),
  ("01432657", 6),
  ("70143256", 8),
  ("01432576", 8),
  ("14325706", 8),
  ("43257016", 8),
  ("32570146", 6),
  ("63257041", 8),
  ("32570461", 8),
  ("25704631", 6),
  ("12570436", 8)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 18 := by decide

theorem based08 : basedOnCheck (List.range 8) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("01765423", 8)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("25704316", 8)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("25704316", 8),
  ("57043126", 8),
  ("70431256", 8),
  ("04312576", 8),
  ("43125706", 6),
  ("64312507", 6),
  ("76431205", 8),
  ("64312075", 8),
  ("43120765", 8),
  ("31207645", 8),
  ("12076435", 6),
  ("51207634", 8),
  ("12076354", 8),
  ("20763514", 8),
  ("07635124", 6),
  ("40763521", 8),
  ("07635241", 8),
  ("76352401", 8),
  ("63524071", 8),
  ("35240761", 6),
  ("13524067", 6),
  ("71352460", 8),
  ("13524670", 8),
  ("35246710", 8),
  ("52467130", 8),
  ("24671350", 6),
  ("02467153", 8),
  ("24671503", 8),
  ("46715023", 6),
  ("34671520", 8),
  ("46715230", 8),
  ("67152340", 8)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 16 := by decide

theorem based09 : basedOnCheck (List.range 8) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("25704316", 8)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("71523460", 6)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("71523460", 6),
  ("07152364", 8),
  ("71523604", 8),
  ("15236074", 8),
  ("52360714", 8),
  ("23607154", 8),
  ("36071524", 6),
  ("43607125", 8),
  ("36071245", 8),
  ("60712435", 8),
  ("07124365", 6),
  ("50712463", 8),
  ("07124653", 8),
  ("71246503", 8),
  ("12465073", 8),
  ("24650713", 6),
  ("32465017", 6),
  ("73246510", 8),
  ("32465170", 8),
  ("24651730", 8),
  ("46517320", 8),
  ("65173240", 6),
  ("06517342", 8),
  ("65173402", 8),
  ("51734062", 8),
  ("17340652", 6),
  ("21734056", 8),
  ("17340526", 8),
  ("73405216", 8),
  ("34052176", 8),
  ("40521736", 6),
  ("64052137", 6)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 18 := by decide

theorem based10 : basedOnCheck (List.range 8) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("71523460", 6)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("76405231", 8)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("76405231", 8),
  ("64052371", 8),
  ("40523761", 8),
  ("05237641", 6),
  ("10523746", 8),
  ("05237416", 8),
  ("52374106", 8),
  ("23741056", 6),
  ("62374150", 8),
  ("23741560", 8),
  ("37415620", 8),
  ("74156230", 6),
  ("07415632", 8),
  ("74156302", 8),
  ("41563072", 8),
  ("15630742", 8),
  ("56307412", 8),
  ("63074152", 6),
  ("26307451", 8),
  ("63074521", 8),
  ("30745261", 6),
  ("13074562", 8),
  ("30745612", 8),
  ("07456132", 8),
  ("74561302", 6),
  ("27456103", 8),
  ("74561023", 8),
  ("45610273", 8),
  ("56102743", 8),
  ("61027453", 6),
  ("36102754", 8),
  ("61027534", 8)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 14 := by decide

theorem based11 : basedOnCheck (List.range 8) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("76405231", 8)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("10275364", 8)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("10275364", 8),
  ("02753614", 8),
  ("27536104", 6),
  ("42753601", 8),
  ("27536041", 8),
  ("75360421", 8),
  ("53604271", 8),
  ("36042751", 6),
  ("13604257", 6),
  ("71360452", 8),
  ("13604572", 8),
  ("36045712", 8),
  ("60457132", 8),
  ("04571362", 6),
  ("20457163", 8),
  ("04571623", 8),
  ("45716203", 8),
  ("57162043", 6),
  ("35716240", 8),
  ("57162430", 8),
  ("71624350", 8),
  ("16243570", 8),
  ("62435710", 6),
  ("06243517", 6),
  ("70624315", 8),
  ("06243175", 8),
  ("62431705", 8),
  ("24317065", 8),
  ("43170625", 6),
  ("54317026", 8),
  ("43170256", 8),
  ("31702546", 6)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 18 := by decide

theorem based12 : basedOnCheck (List.range 8) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("10275364", 8)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("63170245", 8)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("63170245", 8),
  ("31702465", 8),
  ("17024635", 8),
  ("70246315", 8),
  ("02463175", 8),
  ("24631705", 6),
  ("52463107", 6),
  ("75246301", 8),
  ("52463071", 8),
  ("24630751", 8),
  ("46307521", 8),
  ("63075241", 6),
  ("16307542", 8),
  ("63075412", 8),
  ("30754162", 8),
  ("07541632", 6),
  ("20754136", 8),
  ("07541326", 8),
  ("75413206", 8),
  ("54132076", 8),
  ("41320756", 6),
  ("64132057", 6),
  ("76413250", 8),
  ("64132570", 8),
  ("41325760", 8),
  ("13257640", 8),
  ("32576410", 6),
  ("03257614", 8),
  ("32576104", 8),
  ("25761034", 6),
  ("42576130", 8),
  ("25761340", 8)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 16 := by decide

theorem based13 : basedOnCheck (List.range 8) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("63170245", 8)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("57613420", 8)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("57613420", 8),
  ("76134250", 6),
  ("07613452", 8),
  ("76134502", 8),
  ("61345072", 8),
  ("13450762", 8),
  ("34507612", 8),
  ("45076132", 6),
  ("24507631", 8),
  ("45076321", 8),
  ("50763241", 8),
  ("07632451", 6),
  ("10763254", 8),
  ("07632514", 8),
  ("76325104", 8),
  ("63251074", 8),
  ("32510764", 6),
  ("43251067", 6),
  ("74325160", 8),
  ("43251670", 8),
  ("32516740", 8),
  ("25167430", 8),
  ("51674320", 6),
  ("05167423", 8),
  ("51674203", 8),
  ("16742053", 8),
  ("67420513", 6),
  ("36742015", 8),
  ("67420135", 8),
  ("74201365", 8),
  ("42013675", 8),
  ("20136745", 6)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 16 := by decide

theorem based14 : basedOnCheck (List.range 8) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("57613420", 8)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("52013647", 6)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("52013647", 6),
  ("75201346", 8),
  ("52013476", 8),
  ("20134756", 8),
  ("01347526", 6),
  ("60134725", 8),
  ("01347265", 8),
  ("13472605", 8),
  ("34726015", 6),
  ("53472610", 8),
  ("34726150", 8),
  ("47261530", 8),
  ("72615340", 8),
  ("26153470", 8),
  ("61534720", 6),
  ("06153427", 6),
  ("70615324", 8),
  ("06153274", 8),
  ("61532704", 8),
  ("15327064", 8),
  ("53270614", 6),
  ("45327016", 8),
  ("53270146", 8),
  ("32701456", 8),
  ("27014536", 6),
  ("62701435", 8),
  ("27014365", 8),
  ("70143625", 8),
  ("01436275", 8),
  ("14362705", 6),
  ("51436207", 6),
  ("75143602", 8)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 32 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 18 := by decide

theorem based15 : basedOnCheck (List.range 8) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("52013647", 6)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("51436072", 8)) = true := by rfl

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

theorem rows_charge : (rows.map Row.charge).sum = 266 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, charge08, charge09, charge10, charge11, charge12, charge13, charge14, charge15, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 8) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, based08, based09, based10, based11, based12, based13, based14, based15, Bool.and_self]

def suffix15 : List (Row Nat) := rows15

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("52013647", 6)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("51436072", 8)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("57613420", 8)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("63170245", 8)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("10275364", 8)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("76405231", 8)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("71523460", 6)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("25704316", 8)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("01765423", 8)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("62537410", 8)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("34501276", 8)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("47602135", 8)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("17435026", 6)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("60375214", 8)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("34172605", 6)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("74532016", 8)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("70642135", 6)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("51436072", 8)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("70642135", 6)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("51436072", 8)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.Halfar1Parts.C02
