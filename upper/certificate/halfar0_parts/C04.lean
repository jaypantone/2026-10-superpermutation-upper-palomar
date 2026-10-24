module

public import upper.certificate.SeedChecks

@[expose] public section

/-! Consecutive original Halfar0 rows 2048 through 2279.
Each reduction uses at most 32 rows. Every piece includes its outgoing boundary. -/
namespace SuperpermutationUpperBound.Native14.Certificate.Halfar0Parts.C04
open Transport
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def encoded00 : List (String × Nat) := [
  ("54371026", 8),
  ("43710256", 8),
  ("37102546", 6),
  ("63710245", 8),
  ("37102465", 8),
  ("71024635", 8),
  ("10246375", 8),
  ("02463715", 8),
  ("24637105", 6),
  ("52463701", 8),
  ("24637051", 8),
  ("46370521", 8),
  ("63705241", 6),
  ("16370542", 8),
  ("63705412", 8),
  ("37054162", 8),
  ("70541632", 6),
  ("27054136", 8),
  ("70541326", 8),
  ("05413276", 8),
  ("54132706", 8),
  ("41327056", 6),
  ("64132750", 8),
  ("41327560", 8),
  ("13275640", 8),
  ("32756410", 6),
  ("03275614", 8),
  ("32756104", 8),
  ("27561034", 6),
  ("42756130", 8),
  ("27561340", 8),
  ("75613420", 8)
]

def rows00 : List (Row Nat) := encoded00.map (decodeRow 12)

theorem length00 : rows00.length = 32 := by
  rw [rows00, List.length_map]
  rfl

theorem charge00 : (rows00.map Row.charge).sum = 14 := by decide

theorem based00 : basedOnCheck (List.range 8) 12 rows00 = true := by rfl

theorem head00 : rows00.head? = some (decodeRow 12 ("54371026", 8)) := by rfl

theorem checked00 : pathRunsToCheck rows00 (decodeRow 12 ("56134270", 8)) = true := by rfl

def encoded01 : List (String × Nat) := [
  ("56134270", 8),
  ("61342750", 6),
  ("06134257", 6),
  ("70613452", 8),
  ("06134572", 8),
  ("61345702", 8),
  ("13457062", 8),
  ("34570612", 8),
  ("45706132", 6),
  ("24570631", 8),
  ("45706321", 8),
  ("57063241", 8),
  ("70632451", 6),
  ("17063254", 8),
  ("70632514", 8),
  ("06325174", 8),
  ("63251704", 8),
  ("32517064", 6),
  ("43251760", 8),
  ("32517640", 8),
  ("25176430", 8),
  ("51764320", 6),
  ("05176423", 8),
  ("51764203", 8),
  ("17642053", 8),
  ("76420513", 6),
  ("37642015", 8),
  ("76420135", 8),
  ("64201375", 8),
  ("42013765", 8),
  ("20137645", 6),
  ("52013746", 8)
]

def rows01 : List (Row Nat) := encoded01.map (decodeRow 12)

theorem length01 : rows01.length = 32 := by
  rw [rows01, List.length_map]
  rfl

theorem charge01 : (rows01.map Row.charge).sum = 16 := by decide

theorem based01 : basedOnCheck (List.range 8) 12 rows01 = true := by rfl

theorem head01 : rows01.head? = some (decodeRow 12 ("56134270", 8)) := by rfl

theorem checked01 : pathRunsToCheck rows01 (decodeRow 12 ("20137456", 8)) = true := by rfl

def encoded02 : List (String × Nat) := [
  ("20137456", 8),
  ("01374526", 6),
  ("60137425", 8),
  ("01374265", 8),
  ("13742605", 8),
  ("37426015", 6),
  ("53742610", 8),
  ("37426150", 8),
  ("74261530", 8),
  ("42615370", 8),
  ("26153740", 8),
  ("61537420", 6),
  ("06153724", 8),
  ("61537204", 8),
  ("15372064", 8),
  ("53720614", 6),
  ("45372016", 8),
  ("53720146", 8),
  ("37201456", 8),
  ("72014536", 6),
  ("67201435", 8),
  ("72014365", 8),
  ("20143675", 8),
  ("01436725", 8),
  ("14367205", 6),
  ("51436702", 8),
  ("14367052", 8),
  ("43670512", 8),
  ("36705142", 6),
  ("23670541", 8),
  ("36705421", 8),
  ("67054231", 8)
]

def rows02 : List (Row Nat) := encoded02.map (decodeRow 12)

theorem length02 : rows02.length = 32 := by
  rw [rows02, List.length_map]
  rfl

theorem charge02 : (rows02.map Row.charge).sum = 14 := by decide

theorem based02 : basedOnCheck (List.range 8) 12 rows02 = true := by rfl

theorem head02 : rows02.head? = some (decodeRow 12 ("20137456", 8)) := by rfl

theorem checked02 : pathRunsToCheck rows02 (decodeRow 12 ("70542361", 6)) = true := by rfl

def encoded03 : List (String × Nat) := [
  ("70542361", 6),
  ("17054263", 8),
  ("70542613", 8),
  ("05426173", 8),
  ("54261703", 6),
  ("35426107", 6),
  ("73542601", 8),
  ("35426071", 8),
  ("54260731", 8),
  ("42607351", 8),
  ("26073541", 6),
  ("12607345", 8),
  ("26073415", 8),
  ("60734125", 8),
  ("07341265", 8),
  ("73412605", 6),
  ("57341206", 8),
  ("73412056", 8),
  ("34120576", 8),
  ("41205736", 8),
  ("12057346", 6),
  ("61205743", 8),
  ("12057463", 8),
  ("20574613", 8),
  ("05746123", 6),
  ("30574621", 8),
  ("05746231", 8),
  ("57462301", 8),
  ("74623051", 6),
  ("17462350", 8),
  ("74623510", 8),
  ("46235170", 8)
]

def rows03 : List (Row Nat) := encoded03.map (decodeRow 12)

theorem length03 : rows03.length = 32 := by
  rw [rows03, List.length_map]
  rfl

theorem charge03 : (rows03.map Row.charge).sum = 16 := by decide

theorem based03 : basedOnCheck (List.range 8) 12 rows03 = true := by rfl

theorem head03 : rows03.head? = some (decodeRow 12 ("70542361", 6)) := by rfl

theorem checked03 : pathRunsToCheck rows03 (decodeRow 12 ("62351740", 8)) = true := by rfl

def encoded04 : List (String × Nat) := [
  ("62351740", 8),
  ("23517460", 6),
  ("02351764", 8),
  ("23517604", 8),
  ("35176024", 8),
  ("51760234", 6),
  ("45176032", 8),
  ("51760342", 8),
  ("17603452", 6),
  ("21760354", 8),
  ("17603524", 8),
  ("76035214", 8),
  ("60352174", 8),
  ("03521764", 6),
  ("40352167", 6),
  ("74035261", 8),
  ("40352671", 8),
  ("03526741", 8),
  ("35267401", 8),
  ("52674031", 8),
  ("26740351", 6),
  ("12674053", 8),
  ("26740513", 8),
  ("67405123", 8),
  ("74051263", 6),
  ("37405162", 8),
  ("74051632", 8),
  ("40516372", 8),
  ("05163742", 8),
  ("51637402", 6),
  ("25163704", 8),
  ("51637024", 8)
]

def rows04 : List (Row Nat) := encoded04.map (decodeRow 12)

theorem length04 : rows04.length = 32 := by
  rw [rows04, List.length_map]
  rfl

theorem charge04 : (rows04.map Row.charge).sum = 16 := by decide

theorem based04 : basedOnCheck (List.range 8) 12 rows04 = true := by rfl

theorem head04 : rows04.head? = some (decodeRow 12 ("62351740", 8)) := by rfl

theorem checked04 : pathRunsToCheck rows04 (decodeRow 12 ("16370254", 8)) = true := by rfl

def encoded05 : List (String × Nat) := [
  ("16370254", 8),
  ("63702514", 6),
  ("46370215", 8),
  ("63702145", 8),
  ("37021465", 8),
  ("70214635", 6),
  ("57021436", 8),
  ("70214356", 8),
  ("02143576", 8),
  ("21435706", 8),
  ("14357026", 6),
  ("61435720", 8),
  ("14357260", 8),
  ("43572610", 6),
  ("04357216", 8),
  ("43572106", 8),
  ("35721046", 8),
  ("57210436", 6),
  ("65721034", 8),
  ("57210364", 8),
  ("72103654", 8),
  ("21036574", 8),
  ("10365724", 6),
  ("41036527", 6),
  ("74103625", 8),
  ("41036275", 8),
  ("10362745", 8),
  ("03627415", 8),
  ("36274105", 8),
  ("62741035", 6),
  ("56274130", 8),
  ("62741350", 8)
]

def rows05 : List (Row Nat) := encoded05.map (decodeRow 12)

theorem length05 : rows05.length = 32 := by
  rw [rows05, List.length_map]
  rfl

theorem charge05 : (rows05.map Row.charge).sum = 16 := by decide

theorem based05 : basedOnCheck (List.range 8) 12 rows05 = true := by rfl

theorem head05 : rows05.head? = some (decodeRow 12 ("16370254", 8)) := by rfl

theorem checked05 : pathRunsToCheck rows05 (decodeRow 12 ("27413560", 6)) = true := by rfl

def encoded06 : List (String × Nat) := [
  ("27413560", 6),
  ("02741365", 8),
  ("27413605", 8),
  ("74136025", 8),
  ("41360275", 8),
  ("13602745", 8),
  ("36027415", 6),
  ("53602714", 8),
  ("36027154", 8),
  ("60271534", 6),
  ("46027135", 8),
  ("60271345", 8),
  ("02713465", 8),
  ("27134605", 8),
  ("71346025", 6),
  ("57134620", 8),
  ("71346250", 8),
  ("13462570", 8),
  ("34625710", 8),
  ("46257130", 6),
  ("04625731", 8),
  ("46257301", 8),
  ("62573041", 8),
  ("25730461", 6),
  ("12573064", 8),
  ("25730614", 8),
  ("57306124", 6),
  ("45730621", 8),
  ("57306241", 8),
  ("73062451", 8),
  ("30624571", 8),
  ("06245731", 8)
]

def rows06 : List (Row Nat) := encoded06.map (decodeRow 12)

theorem length06 : rows06.length = 32 := by
  rw [rows06, List.length_map]
  rfl

theorem charge06 : (rows06.map Row.charge).sum = 14 := by decide

theorem based06 : basedOnCheck (List.range 8) 12 rows06 = true := by rfl

theorem head06 : rows06.head? = some (decodeRow 12 ("27413560", 6)) := by rfl

theorem checked06 : pathRunsToCheck rows06 (decodeRow 12 ("62457301", 6)) = true := by rfl

def encoded07 : List (String × Nat) := [
  ("62457301", 6),
  ("16245703", 8),
  ("62457013", 8),
  ("24570163", 8),
  ("45701623", 6),
  ("34570126", 8),
  ("45701236", 8),
  ("57012346", 8)
]

def rows07 : List (Row Nat) := encoded07.map (decodeRow 12)

theorem length07 : rows07.length = 8 := by
  rw [rows07, List.length_map]
  rfl

theorem charge07 : (rows07.map Row.charge).sum = 4 := by decide

theorem based07 : basedOnCheck (List.range 8) 12 rows07 = true := by rfl

theorem head07 : rows07.head? = some (decodeRow 12 ("62457301", 6)) := by rfl

theorem checked07 : pathRunsToCheck rows07 (decodeRow 12 ("70123456", 6)) = true := by rfl

def encoded : List (String × Nat) :=
  encoded00 ++
  encoded01 ++
  encoded02 ++
  encoded03 ++
  encoded04 ++
  encoded05 ++
  encoded06 ++
  encoded07

def rows : List (Row Nat) := encoded.map (decodeRow 12)

theorem rows_blocks : rows =
  rows00 ++
  rows01 ++
  rows02 ++
  rows03 ++
  rows04 ++
  rows05 ++
  rows06 ++
  rows07 := by
  simp only [rows, encoded, List.map_append, rows00, rows01, rows02, rows03, rows04, rows05, rows06, rows07]

theorem rows_length : rows.length = 232 := by
  simp only [rows_blocks, List.length_append, length00, length01, length02, length03, length04, length05, length06, length07, Nat.reduceAdd]

theorem rows_charge : (rows.map Row.charge).sum = 110 := by
  simp only [rows_blocks, List.map_append, List.sum_append, charge00, charge01, charge02, charge03, charge04, charge05, charge06, charge07, Nat.reduceAdd]

theorem rows_checked : basedOnCheck (List.range 8) 12 rows = true := by
  simp only [rows_blocks, basedOnCheck_append, based00, based01, based02, based03, based04, based05, based06, based07, Bool.and_self]

def suffix07 : List (Row Nat) := rows07

theorem suffix07_head : suffix07.head? = some (decodeRow 12 ("62457301", 6)) :=
  head07

theorem suffix07_path : PathRunsTo suffix07 (decodeRow 12 ("70123456", 6)) :=
  pathRunsToCheck_sound checked07

def suffix06 : List (Row Nat) := rows06 ++ suffix07

theorem suffix06_head : suffix06.head? = some (decodeRow 12 ("27413560", 6)) :=
  head_append_of_head (ys := suffix07) head06

theorem suffix06_path : PathRunsTo suffix06 (decodeRow 12 ("70123456", 6)) :=
  pathRunsTo_append_of_head suffix07_head
    (pathRunsToCheck_sound checked06) suffix07_path

def suffix05 : List (Row Nat) := rows05 ++ suffix06

theorem suffix05_head : suffix05.head? = some (decodeRow 12 ("16370254", 8)) :=
  head_append_of_head (ys := suffix06) head05

theorem suffix05_path : PathRunsTo suffix05 (decodeRow 12 ("70123456", 6)) :=
  pathRunsTo_append_of_head suffix06_head
    (pathRunsToCheck_sound checked05) suffix06_path

def suffix04 : List (Row Nat) := rows04 ++ suffix05

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("62351740", 8)) :=
  head_append_of_head (ys := suffix05) head04

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("70123456", 6)) :=
  pathRunsTo_append_of_head suffix05_head
    (pathRunsToCheck_sound checked04) suffix05_path

def suffix03 : List (Row Nat) := rows03 ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("70542361", 6)) :=
  head_append_of_head (ys := suffix04) head03

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("70123456", 6)) :=
  pathRunsTo_append_of_head suffix04_head
    (pathRunsToCheck_sound checked03) suffix04_path

def suffix02 : List (Row Nat) := rows02 ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("20137456", 8)) :=
  head_append_of_head (ys := suffix03) head02

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("70123456", 6)) :=
  pathRunsTo_append_of_head suffix03_head
    (pathRunsToCheck_sound checked02) suffix03_path

def suffix01 : List (Row Nat) := rows01 ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("56134270", 8)) :=
  head_append_of_head (ys := suffix02) head01

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("70123456", 6)) :=
  pathRunsTo_append_of_head suffix02_head
    (pathRunsToCheck_sound checked01) suffix02_path

def suffix00 : List (Row Nat) := rows00 ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("54371026", 8)) :=
  head_append_of_head (ys := suffix01) head00

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("70123456", 6)) :=
  pathRunsTo_append_of_head suffix01_head
    (pathRunsToCheck_sound checked00) suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, suffix05, suffix06, suffix07, List.append_assoc]

theorem rows_head : rows.head? = some (decodeRow 12 ("54371026", 8)) := by
  rw [rows_eq_suffix]
  exact suffix00_head

theorem rows_path : PathRunsTo rows (decodeRow 12 ("70123456", 6)) := by
  rw [rows_eq_suffix]
  exact suffix00_path

end SuperpermutationUpperBound.Native14.Certificate.Halfar0Parts.C04
