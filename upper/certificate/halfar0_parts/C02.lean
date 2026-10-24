module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original Halfar0 rows 1024 through 1535.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.Halfar0Parts.C02
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("67352014", 8),
  ("73520164", 8),
  ("35201674", 8),
  ("52016734", 8),
  ("20167354", 6),
  ("42016753", 8),
  ("20167543", 8),
  ("01675423", 8),
  ("16754203", 6),
  ("31675402", 8),
  ("16754032", 8),
  ("67540312", 8),
  ("75403162", 6),
  ("27540361", 8),
  ("75403621", 8),
  ("54036271", 8),
  ("40362751", 6),
  ("14036257", 6),
  ("71403652", 8),
  ("14036572", 8),
  ("40365712", 8),
  ("03657142", 8),
  ("36571402", 6),
  ("23657104", 8),
  ("36571024", 8),
  ("65710234", 8),
  ("57102364", 6),
  ("45710263", 8),
  ("57102643", 8),
  ("71026453", 8),
  ("10264573", 8),
  ("02645713", 6)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 16 := by decide

theorem based00 : basedOnCheck (List.range 8) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("67352014", 8)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("30264517", 6)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("30264517", 6),
  ("73026415", 8),
  ("30264175", 8),
  ("02641735", 8),
  ("26417305", 8),
  ("64173025", 8),
  ("41730265", 6),
  ("54173062", 8),
  ("41730652", 8),
  ("17306542", 8),
  ("73065412", 6),
  ("27306514", 8),
  ("73065124", 8),
  ("30651274", 8),
  ("06512734", 8),
  ("65127304", 6),
  ("46512703", 8),
  ("65127043", 8),
  ("51270463", 8),
  ("12704653", 6),
  ("31270456", 8),
  ("12704536", 8),
  ("27045316", 8),
  ("70453126", 6),
  ("67045321", 8),
  ("70453261", 8),
  ("04532671", 8),
  ("45326701", 8),
  ("53267041", 6),
  ("15326740", 8),
  ("53267410", 8),
  ("32674150", 6)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 16 := by decide

theorem based01 : basedOnCheck (List.range 8) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("30264517", 6)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("03267451", 8)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("03267451", 8),
  ("32674501", 8),
  ("26745031", 8),
  ("67450321", 6),
  ("16745023", 8),
  ("67450213", 8),
  ("74502163", 8),
  ("45021673", 8),
  ("50216743", 8),
  ("02167453", 6),
  ("30216754", 8),
  ("02167534", 8),
  ("21675304", 8),
  ("16753024", 6),
  ("41675320", 8),
  ("16753240", 8),
  ("67532410", 8),
  ("75324160", 6),
  ("07532461", 8),
  ("75324601", 8),
  ("53246071", 8),
  ("32460751", 8),
  ("24607531", 6),
  ("12460735", 8),
  ("24607315", 8),
  ("46073125", 8),
  ("60731245", 6),
  ("56073142", 8),
  ("60731452", 8),
  ("07314562", 8),
  ("73145602", 6),
  ("27314506", 8)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 14 := by decide

theorem based02 : basedOnCheck (List.range 8) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("03267451", 8)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("73145026", 8)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("73145026", 8),
  ("31450276", 8),
  ("14502736", 6),
  ("61450237", 6),
  ("76145032", 8),
  ("61450372", 8),
  ("14503762", 8),
  ("45037612", 8),
  ("50376142", 6),
  ("25037641", 8),
  ("50376421", 8),
  ("03764251", 8),
  ("37642501", 8),
  ("76425031", 6),
  ("17642530", 8),
  ("76425310", 8),
  ("64253170", 8),
  ("42531760", 8),
  ("25317640", 6),
  ("02531746", 8),
  ("25317406", 8),
  ("53174026", 8),
  ("31740256", 6),
  ("63174052", 8),
  ("31740562", 8),
  ("17405632", 8),
  ("74056312", 6),
  ("27405613", 8),
  ("74056123", 8),
  ("40561273", 8),
  ("05612743", 8),
  ("56127403", 6)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 16 := by decide

theorem based03 : basedOnCheck (List.range 8) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("73145026", 8)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("35612704", 8)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("35612704", 8),
  ("56127034", 8),
  ("61270354", 8),
  ("12703564", 6),
  ("41270365", 8),
  ("12703645", 8),
  ("27036415", 6),
  ("52703614", 8),
  ("27036154", 8),
  ("70361524", 8),
  ("03615274", 8),
  ("36152704", 6),
  ("43615207", 6),
  ("74361502", 8),
  ("43615072", 8),
  ("36150742", 8),
  ("61507432", 8),
  ("15074362", 8),
  ("50743612", 6),
  ("25074316", 8),
  ("50743126", 8),
  ("07431256", 8),
  ("74312506", 6),
  ("67431205", 8),
  ("74312065", 8),
  ("43120675", 8),
  ("31206745", 8),
  ("12067435", 6),
  ("51206734", 8),
  ("12067354", 8),
  ("20673514", 8),
  ("06735124", 6)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 16 := by decide

theorem based04 : basedOnCheck (List.range 8) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("35612704", 8)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("40673521", 8)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("40673521", 8),
  ("06735241", 8),
  ("67352401", 8),
  ("73524061", 6),
  ("17352460", 8),
  ("73524610", 8),
  ("35246170", 8),
  ("52461730", 8),
  ("24617350", 6),
  ("02461753", 8),
  ("24617503", 8),
  ("46175023", 6),
  ("34617520", 8),
  ("46175230", 8),
  ("61752340", 8),
  ("17523460", 6),
  ("01752364", 8),
  ("17523604", 8),
  ("75236014", 8),
  ("52360174", 8),
  ("23601754", 8),
  ("36017524", 6),
  ("43601725", 8),
  ("36017245", 8),
  ("60172435", 8),
  ("01724365", 6),
  ("50172463", 8),
  ("01724653", 8),
  ("17246503", 8),
  ("72465013", 6),
  ("37246510", 8),
  ("72465130", 8)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 14 := by decide

theorem based05 : basedOnCheck (List.range 8) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("40673521", 8)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("24651370", 8)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("24651370", 8),
  ("46513720", 8),
  ("65137240", 6),
  ("06513742", 8),
  ("65137402", 8),
  ("51374062", 8),
  ("13740652", 6),
  ("21374056", 8),
  ("13740526", 8),
  ("37405216", 8),
  ("74052136", 6),
  ("67405231", 8),
  ("74052361", 8),
  ("40523671", 8),
  ("05236741", 6),
  ("10523647", 6),
  ("71052346", 8),
  ("10523476", 8),
  ("05234716", 8),
  ("52347106", 8),
  ("23471056", 6),
  ("62347150", 8),
  ("23471560", 8),
  ("34715620", 8),
  ("47156230", 6),
  ("04715632", 8),
  ("47156302", 8),
  ("71563042", 8),
  ("15630472", 8),
  ("56304712", 8),
  ("63047152", 6),
  ("26304751", 8)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 16 := by decide

theorem based06 : basedOnCheck (List.range 8) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("24651370", 8)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("63047521", 8)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("63047521", 8),
  ("30475261", 6),
  ("13047562", 8),
  ("30475612", 8),
  ("04756132", 8),
  ("47561302", 6),
  ("24756103", 8),
  ("47561023", 8),
  ("75610243", 8),
  ("56102473", 8),
  ("61024753", 6),
  ("36102457", 6),
  ("73610254", 8),
  ("36102574", 8),
  ("61025734", 8),
  ("10257364", 8),
  ("02573614", 8),
  ("25736104", 6),
  ("42573601", 8),
  ("25736041", 8),
  ("57360421", 8),
  ("73604251", 6),
  ("17360452", 8),
  ("73604512", 8),
  ("36045172", 8),
  ("60451732", 8),
  ("04517362", 6),
  ("20451763", 8),
  ("04517623", 8),
  ("45176203", 8),
  ("51762043", 6),
  ("35176240", 8)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 16 := by decide

theorem based07 : basedOnCheck (List.range 8) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("63047521", 8)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("51762430", 8)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("51762430", 8),
  ("17624350", 8),
  ("76243510", 6),
  ("07624315", 8),
  ("76243105", 8),
  ("62431075", 8),
  ("24310765", 8),
  ("43107625", 6),
  ("54310726", 8),
  ("43107256", 8),
  ("31072546", 6),
  ("63107245", 8),
  ("31072465", 8),
  ("10724635", 8),
  ("07246315", 8),
  ("72463105", 6),
  ("57246301", 8),
  ("72463051", 8),
  ("24630571", 8),
  ("46305721", 8),
  ("63057241", 6),
  ("16305742", 8),
  ("63057412", 8),
  ("30574162", 8),
  ("05741632", 6),
  ("20574136", 8),
  ("05741326", 8),
  ("57413206", 8),
  ("74132056", 6),
  ("67413250", 8),
  ("74132560", 8),
  ("41325670", 8)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 14 := by decide

theorem based08 : basedOnCheck (List.range 8) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("51762430", 8)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("13256740", 8)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("13256740", 8),
  ("32567410", 6),
  ("03256714", 8),
  ("32567104", 8),
  ("25671034", 6),
  ("42567130", 8),
  ("25671340", 8),
  ("56713420", 8),
  ("67134250", 6),
  ("06713452", 8),
  ("67134502", 8),
  ("71345062", 8),
  ("13450672", 8),
  ("34506712", 8),
  ("45067132", 6),
  ("24506731", 8),
  ("45067321", 8),
  ("50673241", 8),
  ("06732451", 6),
  ("10673254", 8),
  ("06732514", 8),
  ("67325104", 8),
  ("73251064", 6),
  ("47325160", 8),
  ("73251640", 8),
  ("32516470", 8),
  ("25164730", 8),
  ("51647320", 6),
  ("05164723", 8),
  ("51647203", 8),
  ("16472053", 8),
  ("64720513", 6)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 16 := by decide

theorem based09 : basedOnCheck (List.range 8) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("13256740", 8)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("36472015", 8)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("36472015", 8),
  ("64720135", 8),
  ("47201365", 8),
  ("72013645", 6),
  ("57201346", 8),
  ("72013456", 8),
  ("20134576", 8),
  ("01345726", 6),
  ("60134527", 6),
  ("76013425", 8),
  ("60134275", 8),
  ("01342765", 8),
  ("13427605", 8),
  ("34276015", 6),
  ("53427610", 8),
  ("34276150", 8),
  ("42761530", 8),
  ("27615340", 8),
  ("76153420", 6),
  ("07615324", 8),
  ("76153204", 8),
  ("61532074", 8),
  ("15320764", 8),
  ("53207614", 6),
  ("45320716", 8),
  ("53207146", 8),
  ("32071456", 8),
  ("20714536", 6),
  ("62071435", 8),
  ("20714365", 8),
  ("07143625", 8),
  ("71436205", 6)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 16 := by decide

theorem based10 : basedOnCheck (List.range 8) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("36472015", 8)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("57143602", 8)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("57143602", 8),
  ("71436052", 8),
  ("14360572", 8),
  ("43605712", 8),
  ("36057142", 6),
  ("23605741", 8),
  ("36057421", 8),
  ("60574231", 8),
  ("05742361", 6),
  ("10574263", 8),
  ("05742613", 8),
  ("57426103", 6),
  ("35742601", 8),
  ("57426031", 8),
  ("74260351", 8),
  ("42603571", 8),
  ("26035741", 6),
  ("12603547", 6),
  ("71260345", 8),
  ("12603475", 8),
  ("26034715", 8),
  ("60347125", 8),
  ("03471265", 8),
  ("34712605", 6),
  ("53471206", 8),
  ("34712056", 8),
  ("47120536", 8),
  ("71205346", 6),
  ("67120543", 8),
  ("71205463", 8),
  ("12054673", 8),
  ("20546713", 8)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 32 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 14 := by decide

theorem based11 : basedOnCheck (List.range 8) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("57143602", 8)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("05467123", 6)) = true := by rfl

def encoded12 : List (String × Nat) := [
  ("05467123", 6),
  ("30546721", 8),
  ("05467231", 8),
  ("54672301", 8),
  ("46723051", 6),
  ("14672350", 8),
  ("46723510", 8),
  ("67235140", 8),
  ("72351460", 6),
  ("07235164", 8),
  ("72351604", 8),
  ("23516074", 8),
  ("35160724", 8),
  ("51607234", 6),
  ("45160732", 8),
  ("51607342", 8),
  ("16073452", 6),
  ("21607354", 8),
  ("16073524", 8),
  ("60735214", 8),
  ("07352164", 6),
  ("40735261", 8),
  ("07352641", 8),
  ("73526401", 8),
  ("35264071", 8),
  ("52640731", 8),
  ("26407351", 6),
  ("12640753", 8),
  ("26407513", 8),
  ("64075123", 8),
  ("40751263", 6),
  ("34075162", 8)
]

def rows12 : List (Row Nat) := encoded12.map (decodeRow 12)

theorem length12 : rows12.length = 32 := by
  rw [rows12, List.length_map]
  rfl

theorem charge12 : (rows12.map Row.charge).sum = 16 := by decide

theorem based12 : basedOnCheck (List.range 8) 12 rows12 = true := by rfl

theorem head12 : rows12.head? = some (decodeRow 12 ("05467123", 6)) := by rfl

theorem checked12 : pathRunsToCheck rows12 (decodeRow 12 ("40751632", 8)) = true := by rfl

def encoded13 : List (String × Nat) := [
  ("40751632", 8),
  ("07516342", 8),
  ("75163402", 6),
  ("27516304", 8),
  ("75163024", 8),
  ("51630274", 8),
  ("16302754", 8),
  ("63027514", 6),
  ("46302715", 8),
  ("63027145", 8),
  ("30271465", 8),
  ("02714635", 6),
  ("50271436", 8),
  ("02714356", 8),
  ("27143506", 8),
  ("71435026", 6),
  ("67143520", 8),
  ("71435260", 8),
  ("14352670", 8),
  ("43526710", 6),
  ("04352617", 6),
  ("70435216", 8),
  ("04352176", 8),
  ("43521706", 8),
  ("35217046", 8),
  ("52170436", 6),
  ("65217034", 8),
  ("52170364", 8),
  ("21703654", 8),
  ("17036524", 6),
  ("41703625", 8),
  ("17036245", 8)
]

def rows13 : List (Row Nat) := encoded13.map (decodeRow 12)

theorem length13 : rows13.length = 32 := by
  rw [rows13, List.length_map]
  rfl

theorem charge13 : (rows13.map Row.charge).sum = 16 := by decide

theorem based13 : basedOnCheck (List.range 8) 12 rows13 = true := by rfl

theorem head13 : rows13.head? = some (decodeRow 12 ("40751632", 8)) := by rfl

theorem checked13 : pathRunsToCheck rows13 (decodeRow 12 ("70362415", 8)) = true := by rfl

def encoded14 : List (String × Nat) := [
  ("70362415", 8),
  ("03624175", 8),
  ("36241705", 8),
  ("62417035", 6),
  ("56241730", 8),
  ("62417350", 8),
  ("24173560", 6),
  ("02417365", 8),
  ("24173605", 8),
  ("41736025", 8),
  ("17360245", 8),
  ("73602415", 6),
  ("57360214", 8),
  ("73602154", 8),
  ("36021574", 8),
  ("60215734", 6),
  ("46021537", 6),
  ("74602135", 8),
  ("46021375", 8),
  ("60213745", 8),
  ("02137465", 8),
  ("21374605", 8),
  ("13746025", 6),
  ("51374620", 8),
  ("13746250", 8),
  ("37462510", 8),
  ("74625130", 6),
  ("07462531", 8),
  ("74625301", 8),
  ("46253071", 8),
  ("62530741", 8),
  ("25307461", 6)
]

def rows14 : List (Row Nat) := encoded14.map (decodeRow 12)

theorem length14 : rows14.length = 32 := by
  rw [rows14, List.length_map]
  rfl

theorem charge14 : (rows14.map Row.charge).sum = 16 := by decide

theorem based14 : basedOnCheck (List.range 8) 12 rows14 = true := by rfl

theorem head14 : rows14.head? = some (decodeRow 12 ("70362415", 8)) := by rfl

theorem checked14 : pathRunsToCheck rows14 (decodeRow 12 ("12530764", 8)) = true := by rfl

def encoded15 : List (String × Nat) := [
  ("12530764", 8),
  ("25307614", 8),
  ("53076124", 6),
  ("45307621", 8),
  ("53076241", 8),
  ("30762451", 8),
  ("07624531", 8),
  ("76245301", 6),
  ("17624503", 8),
  ("76245013", 8),
  ("62450173", 8),
  ("24501763", 8),
  ("45017623", 6),
  ("34501726", 8),
  ("45017236", 8),
  ("50172346", 8),
  ("01723456", 6),
  ("60172354", 8),
  ("01723564", 8),
  ("17235604", 6),
  ("41723506", 8),
  ("17235046", 8),
  ("72350416", 8),
  ("23504176", 8),
  ("35041726", 6),
  ("63504127", 6),
  ("76350421", 8),
  ("63504271", 8),
  ("35042761", 8),
  ("50427631", 8),
  ("04276351", 8),
  ("42763501", 6)
]

def rows15 : List (Row Nat) := encoded15.map (decodeRow 12)

theorem length15 : rows15.length = 32 := by
  rw [rows15, List.length_map]
  rfl

theorem charge15 : (rows15.map Row.charge).sum = 16 := by decide

theorem based15 : basedOnCheck (List.range 8) 12 rows15 = true := by rfl

theorem head15 : rows15.head? = some (decodeRow 12 ("12530764", 8)) := by rfl

theorem checked15 : pathRunsToCheck rows15 (decodeRow 12 ("14276305", 8)) = true := by rfl

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

theorem suffix15_head : suffix15.head? = some (decodeRow 12 ("12530764", 8)) :=
  head15

theorem suffix15_path : PathRunsTo suffix15 (decodeRow 12 ("14276305", 8)) :=
  pathRunsToCheck_sound checked15

def suffix14 : List (Row Nat) := rows14 ++ suffix15

theorem suffix14_head : suffix14.head? = some (decodeRow 12 ("70362415", 8)) :=
  head_append_of_head (ys := suffix15) head14

theorem suffix14_path : PathRunsTo suffix14 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix15_head
    (pathRunsToCheck_sound checked14) suffix15_path

def suffix13 : List (Row Nat) := rows13 ++ suffix14

theorem suffix13_head : suffix13.head? = some (decodeRow 12 ("40751632", 8)) :=
  head_append_of_head (ys := suffix14) head13

theorem suffix13_path : PathRunsTo suffix13 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix14_head
    (pathRunsToCheck_sound checked13) suffix14_path

def suffix12 : List (Row Nat) := rows12 ++ suffix13

theorem suffix12_head : suffix12.head? = some (decodeRow 12 ("05467123", 6)) :=
  head_append_of_head (ys := suffix13) head12

theorem suffix12_path : PathRunsTo suffix12 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix13_head
    (pathRunsToCheck_sound checked12) suffix13_path

def suffix11 : List (Row Nat) := rows11 ++ suffix12

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("57143602", 8)) :=
  head_append_of_head (ys := suffix12) head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix12_head
    (pathRunsToCheck_sound checked11) suffix12_path

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("36472015", 8)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("13256740", 8)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("51762430", 8)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("63047521", 8)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("24651370", 8)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("40673521", 8)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("35612704", 8)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("73145026", 8)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("03267451", 8)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("30264517", 6)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("67352014", 8)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("14276305", 8)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, suffix12, suffix13, suffix14, suffix15, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("67352014", 8)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("14276305", 8)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.Halfar0Parts.C02
