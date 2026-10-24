module

public import upper.pointers.Trace
public import upper.seed_family.Membership
public import upper.pointers.FastSources

@[expose] public section

namespace SuperpermutationUpperBound.Native14.Pointers
open CircleTransport Transport SeedFamily Certificate

def sourcePoint (rows : List (Row Nat)) (prefixes : List Int) (i : Nat) : Option Point :=
  rows[i]?.map fun r=>⟨r,prefixes.getD i 0⟩

theorem sourcePoint_sound {rows : List (Row Nat)} {prefixes : List Int}
    (hs : sourcePrefixCheck rows prefixes 0=true) (i : Nat) {p : Point}
    (hp : sourcePoint rows prefixes i=some p) : p.Occurs rows := by
  unfold sourcePoint at hp
  cases he : rows[i]? with
  | none => simp [he] at hp
  | some r =>
      obtain ⟨hi,hr⟩ := List.getElem?_eq_some_iff.mp he
      rw [he] at hp
      simp only [Option.map_some,Option.some.injEq] at hp
      subst p
      have hh := sourcePrefix_occurrence hs i hi
      simpa only [Point.Occurs,RowOccurrence,hr] using hh

noncomputable def outsidePoint (b : Bool) (i : Nat) : Option Point :=
  fastOutsidePoint b i

theorem outsidePoint_sound (b : Bool) (i : Nat) {p : Point}
    (hp : outsidePoint b i=some p) : p.Occurs (outsideSource b) :=
  fastOutsidePoint_sound b i hp

theorem outsideSource_shape (b : Bool) : Shape 8 (outsideSource b) := by
  cases b with
  | false => exact shape_of_basedOn_range Halfar0.rows_basedOn
  | true => exact shape_of_basedOn_range Halfar1.rows_basedOn

/-- Four offsets are packed least significant bit first, matching the four
ordinary insertions 8,9,10,11. -/
noncomputable def outsideTrace (b : Bool) (p7 : Fin 7) (p8 : Fin 8)
    (p9 : Fin 9) (p10 : Fin 10) (sourceIndex offsetMask : Nat) : Option Point :=
  (outsidePoint b sourceIndex).bind fun p =>
    (liftPoint 6 8 p7 (offsetMask%2) p).bind fun p =>
      (liftPoint 7 9 p8 (offsetMask/2%2) p).bind fun p =>
        (liftPoint 8 10 p9 (offsetMask/4%2) p).bind fun p =>
          liftPoint 9 11 p10 (offsetMask/8%2) p

theorem outsideTrace_sound (b : Bool) (p7 : Fin 7) (p8 : Fin 8)
    (p9 : Fin 9) (p10 : Fin 10) (sourceIndex offsetMask : Nat) {q : Point}
    (hc : outsideTrace b p7 p8 p9 p10 sourceIndex offsetMask=some q) :
    q.Occurs (outsideAt b p7 p8 p9 p10) := by
  simp only [outsideTrace,Option.bind_eq_some_iff] at hc
  obtain ⟨q0,hq0,q1,hq1,q2,hq2,q3,hq3,hq4⟩ := hc
  have hs0 := outsideSource_shape b
  have hs1 := transportWalk_shape 8 (by decide) (outsideSource b) 8 hs0 p7.val
  have hs2 := transportWalk_shape 9 (by decide) _ 9 hs1 p8.val
  have hs3 := transportWalk_shape 10 (by decide) _ 10 hs2 p9.val
  have h0 := outsidePoint_sound b sourceIndex hq0
  have h1 := liftPoint_sound h0 6 8 (by decide) hs0 p7 _ hq1
  have h2 := liftPoint_sound h1 7 9 (by decide) hs1 p8 _ hq2
  have h3 := liftPoint_sound h2 8 10 (by decide) hs2 p9 _ hq3
  exact liftPoint_sound h3 9 11 (by decide) hs3 p10 _ hq4

theorem outsideAt_shape (b : Bool) (p7 : Fin 7) (p8 : Fin 8)
    (p9 : Fin 9) (p10 : Fin 10) : Shape 12 (outsideAt b p7 p8 p9 p10) := by
  exact transportWalk_shape 11 (by decide) _ 11
    (transportWalk_shape 10 (by decide) _ 10
      (transportWalk_shape 9 (by decide) _ 9
        (transportWalk_shape 8 (by decide) _ 8 (outsideSource_shape b) p7.val) p8.val)
      p9.val) p10.val

noncomputable def mixedTrace (i : Fin 22) (sourceIndex lap offset : Nat) : Option Point :=
  if hi : i.val<2 then
    if lap<5 then
      (fastF0Point sourceIndex).bind fun p=>
        liftPoint 9 11 ⟨i.val,by omega⟩ offset ⟨p.row,(lap:Int)*126+p.excess⟩
    else none
  else if hi' : i.val<12 then
    (fastF1Point sourceIndex).bind
      (liftPoint 9 11 ⟨i.val-2,by omega⟩ offset)
  else
    (fastF2Point sourceIndex).bind
      (liftPoint 9 11 ⟨i.val-12,by omega⟩ offset)

theorem mixedTrace_sound (i : Fin 22) (sourceIndex lap offset : Nat) {q : Point}
    (hc : mixedTrace i sourceIndex lap offset=some q) : q.Occurs (mixedAt i) := by
  unfold mixedTrace at hc
  split_ifs at hc with hi hl hi'
  · obtain ⟨p,hp,hq⟩ := Option.bind_eq_some_iff.mp hc
    have ho := fastF0Point_sound sourceIndex hp
    have hr := ho.repeat_lap 5 lap hl
    rw [BlockF0.rows_excess] at hr
    have hs := (shape_of_basedOn_range BlockF0.rows_basedOn).repeatRows 5
    have hrp : (⟨p.row,(lap:Int)*126+p.excess⟩:Point).Occurs (Regularization.repeatRows BlockF0.rows 5) := hr
    have hh := liftPoint_sound hrp 9 11 (by decide) hs ⟨i.val,by omega⟩ offset hq
    simpa only [mixedAt,if_pos hi] using hh
  · obtain ⟨p,hp,hq⟩ := Option.bind_eq_some_iff.mp hc
    have ho := fastF1Point_sound sourceIndex hp
    have hh := liftPoint_sound ho 9 11 (by decide)
      (shape_of_basedOn_range BlockF1.rows_basedOn) ⟨i.val-2,by omega⟩ offset hq
    simpa only [mixedAt,if_neg hi,if_pos hi'] using hh
  · obtain ⟨p,hp,hq⟩ := Option.bind_eq_some_iff.mp hc
    have ho := fastF2Point_sound sourceIndex hp
    have hh := liftPoint_sound ho 9 11 (by decide)
      (shape_of_basedOn_range BlockF2.rows_basedOn) ⟨i.val-12,by omega⟩ offset hq
    simpa only [mixedAt,if_neg hi,if_neg hi'] using hh

theorem mixedAt_shape (i : Fin 22) : Shape 12 (mixedAt i) := by
  unfold mixedAt
  split_ifs with hi hi'
  · exact transportWalk_shape 11 (by decide) _ 11
      ((shape_of_basedOn_range BlockF0.rows_basedOn).repeatRows 5) _
  · exact transportWalk_shape 11 (by decide) _ 11
      (shape_of_basedOn_range BlockF1.rows_basedOn) _
  · exact transportWalk_shape 11 (by decide) _ 11
      (shape_of_basedOn_range BlockF2.rows_basedOn) _

def mapPoint (f : Nat→Nat) (p : Point) : Point := ⟨p.row.map f,p.excess⟩

theorem mapPoint_sound (f : Nat→Nat) {p : Point} {rs : List (Row Nat)}
    (hp : p.Occurs rs) : (mapPoint f p).Occurs (rs.map (Row.map f)) := hp.map f

def relabelPoint (x : List Nat) (p : Point) : Point := mapPoint (Partition.relabelSeven x) p

theorem relabelPoint_sound (x : List Nat) {p : Point} {rs : List (Row Nat)}
    (hp : p.Occurs rs) : (relabelPoint x p).Occurs (rs.map (Row.map (Partition.relabelSeven x))) :=
  hp.map (Partition.relabelSeven x)

theorem shape_relabel (x : List Nat) {n : Nat} {rs : List (Row Nat)} (hs : Shape n rs) :
    Shape n (rs.map (Row.map (Partition.relabelSeven x))) := by
  intro r hr
  obtain ⟨s,hm,rfl⟩ := List.mem_map.mp hr
  simpa only [Row.map_base_length,Row.map_visible] using hs s hm

end SuperpermutationUpperBound.Native14.Pointers
