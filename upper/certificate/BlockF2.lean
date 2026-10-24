module

public import upper.certificate.blockf2_parts.C00
public import upper.certificate.blockf2_parts.C01
public import upper.certificate.blockf2_parts.C02
public import upper.certificate.blockf2_parts.C03

@[expose] public section

/-! Original ordered source walk from `block-7-4-f.txt`.
The literal rows are split into bounded certificates; no row is changed or
reordered. Internal and inter-part boundaries, including the return to the
first row, are checked before the parts are concatenated. -/
namespace SuperpermutationUpperBound.Native14.Certificate.BlockF2
open Transport

def encoded : List (String × Nat) :=
  BlockF2Parts.C00.encoded ++
  BlockF2Parts.C01.encoded ++
  BlockF2Parts.C02.encoded ++
  BlockF2Parts.C03.encoded

def rows : List (Row Nat) := encoded.map (decodeRow 12)

theorem rows_blocks : rows =
  BlockF2Parts.C00.rows ++
  BlockF2Parts.C01.rows ++
  BlockF2Parts.C02.rows ++
  BlockF2Parts.C03.rows := by
  simp only [rows, encoded, List.map_append, BlockF2Parts.C00.rows, BlockF2Parts.C01.rows, BlockF2Parts.C02.rows, BlockF2Parts.C03.rows]

theorem rows_length : rows.length = 2030 := by
  simp only [rows_blocks, List.length_append, BlockF2Parts.C00.rows_length, BlockF2Parts.C01.rows_length, BlockF2Parts.C02.rows_length, BlockF2Parts.C03.rows_length, Nat.reduceAdd]

theorem rows_charge : (rows.map Row.charge).sum = 910 := by
  simp only [rows_blocks, List.map_append, List.sum_append, BlockF2Parts.C00.rows_charge, BlockF2Parts.C01.rows_charge, BlockF2Parts.C02.rows_charge, BlockF2Parts.C03.rows_charge, Nat.reduceAdd]

theorem rows_excess : signedExcess rows = 1120 := by
  simp only [signedExcess, rows_length, rows_charge]
  norm_num

theorem rows_basedOn : BasedOn (List.range 11) 12 rows := by
  apply basedOn_of_check
  simp only [rows_blocks, basedOnCheck_append, BlockF2Parts.C00.rows_checked, BlockF2Parts.C01.rows_checked, BlockF2Parts.C02.rows_checked, BlockF2Parts.C03.rows_checked, Bool.and_self]

def suffix03 : List (Row Nat) := BlockF2Parts.C03.rows

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("345A6091287", 11)) :=
  BlockF2Parts.C03.rows_head

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("9A012347568", 11)) :=
  BlockF2Parts.C03.rows_path

def suffix02 : List (Row Nat) := BlockF2Parts.C02.rows ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("5601293A487", 11)) :=
  head_append_of_head (ys := suffix03) BlockF2Parts.C02.rows_head

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix03_head BlockF2Parts.C02.rows_path suffix03_path

def suffix01 : List (Row Nat) := BlockF2Parts.C01.rows ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("1A234956807", 9)) :=
  head_append_of_head (ys := suffix02) BlockF2Parts.C01.rows_head

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix02_head BlockF2Parts.C01.rows_path suffix02_path

def suffix00 : List (Row Nat) := BlockF2Parts.C00.rows ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("9A012347568", 11)) :=
  head_append_of_head (ys := suffix01) BlockF2Parts.C00.rows_head

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("9A012347568", 11)) :=
  pathRunsTo_append_of_head suffix01_head BlockF2Parts.C00.rows_path suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, List.append_assoc]

theorem rows_closed : ClosedTrail rows := by
  rw [rows_eq_suffix]
  exact closedTrail_of_head_and_path suffix00_head suffix00_path

theorem rows_orbit_count : Nat.gcd 10 (signedExcess rows).natAbs = 10 := by
  rw [rows_excess]
  decide

end SuperpermutationUpperBound.Native14.Certificate.BlockF2
