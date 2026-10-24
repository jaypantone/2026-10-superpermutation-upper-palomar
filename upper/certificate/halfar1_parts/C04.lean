module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original Halfar1 rows 2048 through 2423.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.Halfar1Parts.C04
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("37601524", 6),
  ("43760125", 8),
  ("37601245", 8),
  ("76012435", 8),
  ("60124375", 8),
  ("01243765", 6),
  ("50124367", 6),
  ("75012463", 8),
  ("50124673", 8),
  ("01246753", 8),
  ("12467503", 8),
  ("24675013", 6),
  ("32467510", 8),
  ("24675130", 8),
  ("46751320", 8),
  ("67513240", 6),
  ("06751342", 8),
  ("67513402", 8),
  ("75134062", 8),
  ("51340672", 8),
  ("13406752", 6),
  ("21340657", 6),
  ("72134056", 8),
  ("21340576", 8),
  ("13405726", 8),
  ("34057216", 8),
  ("40572136", 6),
  ("64057231", 8),
  ("40572361", 8),
  ("05723641", 6),
  ("10572346", 8),
  ("05723416", 8)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 18 := by decide

theorem based00 : basedOnCheck (List.range 8) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("37601524", 6)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("57234106", 8)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("57234106", 8),
  ("72341056", 6),
  ("67234150", 8),
  ("72341560", 8),
  ("23415670", 8),
  ("34156720", 8),
  ("41567230", 6),
  ("04156732", 8),
  ("41567302", 8),
  ("15673042", 8),
  ("56730412", 8),
  ("67304152", 6),
  ("26730451", 8),
  ("67304521", 8),
  ("73045261", 6),
  ("17304562", 8),
  ("73045612", 8),
  ("30456172", 8),
  ("04561732", 8),
  ("45617302", 8),
  ("56173042", 6),
  ("25617340", 8),
  ("56173420", 8),
  ("61734250", 6),
  ("06173452", 8),
  ("61734502", 8),
  ("17345062", 8),
  ("73450612", 8),
  ("34506172", 8),
  ("45061732", 6),
  ("24506137", 6),
  ("72450631", 8)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 16 := by decide

theorem based01 : basedOnCheck (List.range 8) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("57234106", 8)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("24506371", 8)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("24506371", 8),
  ("45063721", 8),
  ("50637241", 8),
  ("06372451", 6),
  ("10637254", 8),
  ("06372514", 8),
  ("63725104", 8),
  ("37251064", 6),
  ("43725160", 8),
  ("37251640", 8),
  ("72516430", 8),
  ("25164370", 8),
  ("51643720", 6),
  ("05164327", 6),
  ("70516423", 8),
  ("05164273", 8),
  ("51642703", 8),
  ("16427053", 8),
  ("64270513", 6),
  ("36427015", 8),
  ("64270135", 8),
  ("42701365", 8),
  ("27013645", 6),
  ("52701346", 8),
  ("27013456", 8),
  ("70134526", 6),
  ("67013425", 8),
  ("70134265", 8),
  ("01342675", 8),
  ("13426705", 8),
  ("34267015", 6),
  ("53426710", 8)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 16 := by decide

theorem based02 : basedOnCheck (List.range 8) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("24506371", 8)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("34267150", 8)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("34267150", 8),
  ("42671530", 8),
  ("26715340", 6),
  ("02671543", 8),
  ("26715403", 8),
  ("67154023", 8),
  ("71540263", 8),
  ("15402673", 8),
  ("54026713", 6),
  ("35402617", 6),
  ("73540216", 8),
  ("35402176", 8),
  ("54021736", 8),
  ("40217356", 6),
  ("64021753", 8),
  ("40217563", 8),
  ("02175643", 8),
  ("21756403", 6),
  ("32175604", 8),
  ("21756034", 8),
  ("17560324", 8),
  ("75603214", 8),
  ("56032174", 8),
  ("60321754", 6),
  ("46032157", 6),
  ("74603251", 8),
  ("46032571", 8),
  ("60325741", 8),
  ("03257461", 8),
  ("32574601", 6),
  ("13257406", 8),
  ("32574016", 8)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 16 := by decide

theorem based03 : basedOnCheck (List.range 8) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("34267150", 8)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("25740136", 8)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("25740136", 8),
  ("57401326", 6),
  ("65740123", 8),
  ("57401263", 8),
  ("74012653", 8),
  ("40126573", 8),
  ("01265743", 6),
  ("30126547", 6),
  ("73012645", 8),
  ("30126475", 8),
  ("01264735", 8),
  ("12647305", 8),
  ("26473015", 6),
  ("52647310", 8),
  ("26473150", 8),
  ("64731520", 8),
  ("47315260", 6),
  ("04731562", 8),
  ("47315602", 8),
  ("73156042", 6),
  ("27315640", 8),
  ("73156420", 8),
  ("31564270", 8),
  ("15642730", 8),
  ("56427310", 6),
  ("05642713", 8),
  ("56427103", 8),
  ("64271053", 8),
  ("42710563", 8),
  ("27105643", 6),
  ("32710546", 8),
  ("27105436", 8)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 16 := by decide

theorem based04 : basedOnCheck (List.range 8) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("25740136", 8)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("71054326", 8)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("71054326", 8),
  ("10543276", 8),
  ("05432716", 6),
  ("60543217", 6),
  ("76054312", 8),
  ("60543172", 8),
  ("05431762", 8),
  ("54317602", 8),
  ("43176052", 6),
  ("24317650", 8),
  ("43176520", 8),
  ("31765240", 8),
  ("17652430", 6),
  ("01765234", 8),
  ("17652304", 8),
  ("76523014", 8),
  ("65230174", 8),
  ("52301764", 6),
  ("45230167", 6),
  ("74523061", 8),
  ("45230671", 8),
  ("52306741", 8),
  ("23067451", 8),
  ("30674521", 6),
  ("13067425", 8),
  ("30674215", 8),
  ("06742135", 6),
  ("50674231", 8),
  ("06742351", 8),
  ("67423501", 8),
  ("74235061", 6),
  ("17423560", 8)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 18 := by decide

theorem based05 : basedOnCheck (List.range 8) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("71054326", 8)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("74235610", 8)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("74235610", 8),
  ("42356170", 8),
  ("23561740", 8),
  ("35617420", 8),
  ("56174230", 6),
  ("05617432", 8),
  ("56174302", 8),
  ("61743052", 8),
  ("17430562", 6),
  ("21743065", 8),
  ("17430625", 8),
  ("74306215", 6),
  ("57430612", 8),
  ("74306152", 8),
  ("43061572", 8),
  ("30615742", 8),
  ("06157432", 6),
  ("20615734", 8),
  ("06157324", 8),
  ("61573204", 8),
  ("15732064", 8),
  ("57320614", 6),
  ("45732016", 8),
  ("57320146", 8),
  ("73201456", 8),
  ("32014576", 8),
  ("20145736", 6),
  ("62014537", 6),
  ("76201435", 8),
  ("62014375", 8),
  ("20143765", 8),
  ("01437625", 8)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 14 := by decide

theorem based06 : basedOnCheck (List.range 8) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("74235610", 8)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("14376205", 6)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("14376205", 6),
  ("51437602", 8),
  ("14376052", 8),
  ("43760512", 8),
  ("37605142", 6),
  ("23760541", 8),
  ("37605421", 8),
  ("76054231", 8),
  ("60542371", 8),
  ("05423761", 6),
  ("10542367", 6),
  ("71054263", 8),
  ("10542673", 8),
  ("05426713", 8),
  ("54267103", 6),
  ("35426701", 8),
  ("54267031", 8),
  ("42670351", 8),
  ("26703541", 6),
  ("12670345", 8),
  ("26703415", 8),
  ("67034125", 8),
  ("70341265", 8),
  ("03412675", 8),
  ("34126705", 6),
  ("53412607", 6),
  ("75341206", 8),
  ("53412076", 8),
  ("34120756", 8),
  ("41207536", 8),
  ("12075346", 6),
  ("61207543", 8)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 32 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 18 := by decide

theorem based07 : basedOnCheck (List.range 8) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("14376205", 6)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("12075463", 8)) = true := by rfl

def encoded08 : List (String × Nat) := [
  ("12075463", 8),
  ("20754613", 8),
  ("07546123", 6),
  ("30754621", 8),
  ("07546231", 8),
  ("75462301", 8),
  ("54623071", 8),
  ("46230751", 6),
  ("14623057", 6),
  ("71462350", 8),
  ("14623570", 8),
  ("46235710", 8),
  ("62357140", 8),
  ("23571460", 6),
  ("02357164", 8),
  ("23571604", 8),
  ("35716024", 8),
  ("57160234", 6),
  ("45716032", 8),
  ("57160342", 8),
  ("71603452", 6),
  ("27160354", 8),
  ("71603524", 8),
  ("16035274", 8),
  ("60352714", 8),
  ("03527164", 6),
  ("40352761", 8),
  ("03527641", 8),
  ("35276401", 8),
  ("52764031", 8),
  ("27640351", 6),
  ("12764053", 8)
]

def rows08 : List (Row Nat) := encoded08.map (decodeRow 12)

theorem length08 : rows08.length = 32 := by
  rw [rows08, List.length_map]
  rfl

theorem charge08 : (rows08.map Row.charge).sum = 16 := by decide

theorem based08 : basedOnCheck (List.range 8) 12 rows08 = true := by rfl

theorem head08 : rows08.head? = some (decodeRow 12 ("12075463", 8)) := by rfl

theorem checked08 : pathRunsToCheck rows08 (decodeRow 12 ("27640513", 8)) = true := by rfl

def encoded09 : List (String × Nat) := [
  ("27640513", 8),
  ("76405123", 8),
  ("64051273", 8),
  ("40512763", 6),
  ("34051267", 6),
  ("73405162", 8),
  ("34051672", 8),
  ("40516732", 8),
  ("05167342", 8),
  ("51673402", 6),
  ("25167304", 8),
  ("51673024", 8),
  ("16730254", 8),
  ("67302514", 6),
  ("46730215", 8),
  ("67302145", 8),
  ("73021465", 8),
  ("30214675", 8),
  ("02146735", 6),
  ("50214637", 6),
  ("75021436", 8),
  ("50214376", 8),
  ("02143756", 8),
  ("21437506", 8),
  ("14375026", 6),
  ("61437520", 8),
  ("14375260", 8),
  ("43752610", 6),
  ("04375216", 8),
  ("43752106", 8),
  ("37521046", 8),
  ("75210436", 6)
]

def rows09 : List (Row Nat) := encoded09.map (decodeRow 12)

theorem length09 : rows09.length = 32 := by
  rw [rows09, List.length_map]
  rfl

theorem charge09 : (rows09.map Row.charge).sum = 18 := by decide

theorem based09 : basedOnCheck (List.range 8) 12 rows09 = true := by rfl

theorem head09 : rows09.head? = some (decodeRow 12 ("27640513", 8)) := by rfl

theorem checked09 : pathRunsToCheck rows09 (decodeRow 12 ("67521034", 8)) = true := by rfl

def encoded10 : List (String × Nat) := [
  ("67521034", 8),
  ("75210364", 8),
  ("52103674", 8),
  ("21036754", 8),
  ("10367524", 6),
  ("41036725", 8),
  ("10367245", 8),
  ("03672415", 8),
  ("36724105", 8),
  ("67241035", 6),
  ("56724130", 8),
  ("67241350", 8),
  ("72413560", 6),
  ("07241365", 8),
  ("72413605", 8),
  ("24136075", 8),
  ("41360725", 8),
  ("13607245", 8),
  ("36072415", 6),
  ("53607214", 8),
  ("36072154", 8),
  ("60721534", 6),
  ("46072135", 8),
  ("60721345", 8),
  ("07213465", 8),
  ("72134605", 8),
  ("21346075", 8),
  ("13460725", 6),
  ("51346027", 6),
  ("75134620", 8),
  ("51346270", 8),
  ("13462750", 8)
]

def rows10 : List (Row Nat) := encoded10.map (decodeRow 12)

theorem length10 : rows10.length = 32 := by
  rw [rows10, List.length_map]
  rfl

theorem charge10 : (rows10.map Row.charge).sum = 14 := by decide

theorem based10 : basedOnCheck (List.range 8) 12 rows10 = true := by rfl

theorem head10 : rows10.head? = some (decodeRow 12 ("67521034", 8)) := by rfl

theorem checked10 : pathRunsToCheck rows10 (decodeRow 12 ("34627510", 8)) = true := by rfl

def encoded11 : List (String × Nat) := [
  ("34627510", 8),
  ("46275130", 6),
  ("04627531", 8),
  ("46275301", 8),
  ("62753041", 8),
  ("27530461", 6),
  ("12753064", 8),
  ("27530614", 8),
  ("75306124", 6),
  ("47530621", 8),
  ("75306241", 8),
  ("53062471", 8),
  ("30624751", 8),
  ("06247531", 8),
  ("62475301", 6),
  ("16247503", 8),
  ("62475013", 8),
  ("24750163", 8),
  ("47501623", 6),
  ("34750126", 8),
  ("47501236", 8),
  ("75012346", 8),
  ("50123476", 8),
  ("01234756", 6)
]

def rows11 : List (Row Nat) := encoded11.map (decodeRow 12)

theorem length11 : rows11.length = 24 := by
  rw [rows11, List.length_map]
  rfl

theorem charge11 : (rows11.map Row.charge).sum = 12 := by decide

theorem based11 : basedOnCheck (List.range 8) 12 rows11 = true := by rfl

theorem head11 : rows11.head? = some (decodeRow 12 ("34627510", 8)) := by rfl

theorem checked11 : pathRunsToCheck rows11 (decodeRow 12 ("60123457", 6)) = true := by rfl

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
  encoded11

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
  rows11 := by
  simp only [rows, encoded, List.map_append, rows00, rows01, rows02, rows03, rows04, rows05, rows06, rows07, rows08, rows09, rows10, rows11]

theorem rows_length : rows.length = 376 := by
  simp only [rows_blocks, List.length_append, length00, length01, length02, length03, length04, length05, length06, length07, length08, length09, length10, length11, Nat.reduceAdd]

theorem rows_charge : (rows.map Row.charge).sum = 192 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, charge08, charge09, charge10, charge11, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 8) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, based08, based09, based10, based11, Bool.and_self]

def suffix11 : List (Row Nat) := rows11

theorem suffix11_head : suffix11.head? = some (decodeRow 12 ("34627510", 8)) :=
  head11

theorem suffix11_path : PathRunsTo suffix11 (decodeRow 12 ("60123457", 6)) :=
  pathRunsToCheck_sound checked11

def suffix10 : List (Row Nat) := rows10 ++ suffix11

theorem suffix10_head : suffix10.head? = some (decodeRow 12 ("67521034", 8)) :=
  head_append_of_head (ys := suffix11) head10

theorem suffix10_path : PathRunsTo suffix10 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix11_head
    (pathRunsToCheck_sound checked10) suffix11_path

def suffix09 : List (Row Nat) := rows09 ++ suffix10

theorem suffix09_head : suffix09.head? = some (decodeRow 12 ("27640513", 8)) :=
  head_append_of_head (ys := suffix10) head09

theorem suffix09_path : PathRunsTo suffix09 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix10_head
    (pathRunsToCheck_sound checked09) suffix10_path

def suffix08 : List (Row Nat) := rows08 ++ suffix09

theorem suffix08_head : suffix08.head? = some (decodeRow 12 ("12075463", 8)) :=
  head_append_of_head (ys := suffix09) head08

theorem suffix08_path : PathRunsTo suffix08 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix09_head
    (pathRunsToCheck_sound checked08) suffix09_path

def suffix07 : List (Row Nat) := rows07 ++ suffix08

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("14376205", 6)) :=
  head_append_of_head (ys := suffix08) head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix08_head
    (pathRunsToCheck_sound checked07) suffix08_path

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("74235610", 8)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("71054326", 8)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("25740136", 8)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("34267150", 8)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("24506371", 8)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("57234106", 8)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("37601524", 6)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, suffix08, suffix09, suffix10, suffix11, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("37601524", 6)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("60123457", 6)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.Halfar1Parts.C04
