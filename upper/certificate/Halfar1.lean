module

public import upper.certificate.halfar1_parts.C00
public import upper.certificate.halfar1_parts.C01
public import upper.certificate.halfar1_parts.C02
public import upper.certificate.halfar1_parts.C03
public import upper.certificate.halfar1_parts.C04

@[expose] public section

/-! Original ordered source walk from `halfar-n10-selection.txt`.
The literal rows are split into bounded certificates; no row is changed or
reordered. Internal and inter-part boundaries, including the return to the
first row, are checked before the parts are concatenated. -/
namespace SuperpermutationUpperBound.Native14.Certificate.Halfar1
open Transport

def encoded : List (String × Nat) :=
  Halfar1Parts.C00.encoded ++
  Halfar1Parts.C01.encoded ++
  Halfar1Parts.C02.encoded ++
  Halfar1Parts.C03.encoded ++
  Halfar1Parts.C04.encoded

def rows : List (Row Nat) := encoded.map (decodeRow 12)

theorem rows_blocks : rows =
  Halfar1Parts.C00.rows ++
  Halfar1Parts.C01.rows ++
  Halfar1Parts.C02.rows ++
  Halfar1Parts.C03.rows ++
  Halfar1Parts.C04.rows := by
  simp only [rows, encoded, List.map_append, Halfar1Parts.C00.rows, Halfar1Parts.C01.rows, Halfar1Parts.C02.rows, Halfar1Parts.C03.rows, Halfar1Parts.C04.rows]

theorem rows_length : rows.length = 2424 := by
  simp only [rows_blocks, List.length_append, Halfar1Parts.C00.rows_length, Halfar1Parts.C01.rows_length, Halfar1Parts.C02.rows_length, Halfar1Parts.C03.rows_length, Halfar1Parts.C04.rows_length, Nat.reduceAdd]

theorem rows_charge : (rows.map Row.charge).sum = 1248 := by
  simp only [rows_blocks, List.map_append, List.sum_append, Halfar1Parts.C00.rows_charge, Halfar1Parts.C01.rows_charge, Halfar1Parts.C02.rows_charge, Halfar1Parts.C03.rows_charge, Halfar1Parts.C04.rows_charge, Nat.reduceAdd]

theorem rows_excess : signedExcess rows = 1176 := by
  simp only [signedExcess, rows_length, rows_charge]
  norm_num

theorem rows_basedOn : BasedOn (List.range 8) 12 rows := by
  apply basedOn_of_check
  simp only [rows_blocks, basedOnCheck_append, Halfar1Parts.C00.rows_checked, Halfar1Parts.C01.rows_checked, Halfar1Parts.C02.rows_checked, Halfar1Parts.C03.rows_checked, Halfar1Parts.C04.rows_checked, Bool.and_self]

def suffix04 : List (Row Nat) := Halfar1Parts.C04.rows

theorem suffix04_head : suffix04.head? = some (decodeRow 12 ("37601524", 6)) :=
  Halfar1Parts.C04.rows_head

theorem suffix04_path : PathRunsTo suffix04 (decodeRow 12 ("60123457", 6)) :=
  Halfar1Parts.C04.rows_path

def suffix03 : List (Row Nat) := Halfar1Parts.C03.rows ++ suffix04

theorem suffix03_head : suffix03.head? = some (decodeRow 12 ("51436072", 8)) :=
  head_append_of_head (ys := suffix04) Halfar1Parts.C03.rows_head

theorem suffix03_path : PathRunsTo suffix03 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix04_head Halfar1Parts.C03.rows_path suffix04_path

def suffix02 : List (Row Nat) := Halfar1Parts.C02.rows ++ suffix03

theorem suffix02_head : suffix02.head? = some (decodeRow 12 ("70642135", 6)) :=
  head_append_of_head (ys := suffix03) Halfar1Parts.C02.rows_head

theorem suffix02_path : PathRunsTo suffix02 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix03_head Halfar1Parts.C02.rows_path suffix03_path

def suffix01 : List (Row Nat) := Halfar1Parts.C01.rows ++ suffix02

theorem suffix01_head : suffix01.head? = some (decodeRow 12 ("62473105", 8)) :=
  head_append_of_head (ys := suffix02) Halfar1Parts.C01.rows_head

theorem suffix01_path : PathRunsTo suffix01 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix02_head Halfar1Parts.C01.rows_path suffix02_path

def suffix00 : List (Row Nat) := Halfar1Parts.C00.rows ++ suffix01

theorem suffix00_head : suffix00.head? = some (decodeRow 12 ("60123457", 6)) :=
  head_append_of_head (ys := suffix01) Halfar1Parts.C00.rows_head

theorem suffix00_path : PathRunsTo suffix00 (decodeRow 12 ("60123457", 6)) :=
  pathRunsTo_append_of_head suffix01_head Halfar1Parts.C00.rows_path suffix01_path

theorem rows_eq_suffix : rows = suffix00 := by
  rw [rows_blocks]
  simp only [suffix00, suffix01, suffix02, suffix03, suffix04, List.append_assoc]

theorem rows_closed : ClosedTrail rows := by
  rw [rows_eq_suffix]
  exact closedTrail_of_head_and_path suffix00_head suffix00_path

theorem rows_orbit_count : Nat.gcd 7 (signedExcess rows).natAbs = 7 := by
  rw [rows_excess]
  decide

end SuperpermutationUpperBound.Native14.Certificate.Halfar1
