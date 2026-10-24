module

public import upper.certificate.blockf0_parts.C00
public import upper.certificate.blockf0_parts.C01

@[expose] public section

/-! Original ordered source walk from `block-7-4-f.txt`.
The literal rows are split into bounded certificates; no row is changed or
reordered. Internal and inter-part boundaries, including the return to the
first row, are checked before the parts are concatenated. -/
namespace SuperpermutationUpperBound.Native14.Certificate.BlockF0
open Transport

def encoded : List (String × Nat) :=
  BlockF0Parts.C00.encoded ++
  BlockF0Parts.C01.encoded

def rows : List (Row Nat) := encoded.map (decodeRow 12)

theorem rows_blocks : rows =
  BlockF0Parts.C00.rows ++
  BlockF0Parts.C01.rows := by
  simp only [rows, encoded, List.map_append, BlockF0Parts.C00.rows, BlockF0Parts.C01.rows]

theorem rows_length : rows.length = 714 := by
  simp only [rows_blocks, List.length_append, BlockF0Parts.C00.rows_length, BlockF0Parts.C01.rows_length, Nat.reduceAdd]

theorem rows_charge : (rows.map Row.charge).sum = 588 := by
  simp only [rows_blocks, List.map_append, List.sum_append, BlockF0Parts.C00.rows_charge, BlockF0Parts.C01.rows_charge, Nat.reduceAdd]

theorem rows_excess : signedExcess rows = 126 := by
  simp only [signedExcess, rows_length, rows_charge]
  norm_num

theorem rows_basedOn : BasedOn (List.range 11) 12 rows := by
  apply basedOn_of_check
  simp only [rows_blocks, basedOnCheck_append, BlockF0Parts.C00.rows_checked, BlockF0Parts.C01.rows_checked, Bool.and_self]

def suffix01 : List (Row Nat) := BlockF0Parts.C01.rows

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("80A12345679", 11)) :=
  BlockF0Parts.C01.rows_head

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("0123456789A", 9)) :=
  BlockF0Parts.C01.rows_path

def suffix00 : List (Row Nat) := BlockF0Parts.C00.rows ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("0123456789A", 9)) :=
  head_append_of_head (ys := suffix01) BlockF0Parts.C00.rows_head

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("0123456789A", 9)) :=
  pathRunsTo_append_of_head suffix01_head BlockF0Parts.C00.rows_path suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, List.append_assoc]

theorem rows_closed : ClosedTrail rows := by
  rw [rows_eq_suffix]
  exact closedTrail_of_head_and_path suffix00_head suffix00_path

theorem rows_orbit_count : Nat.gcd 10 (signedExcess rows).natAbs = 2 := by
  rw [rows_excess]
  decide

end SuperpermutationUpperBound.Native14.Certificate.BlockF0
