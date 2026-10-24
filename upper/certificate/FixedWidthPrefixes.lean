module

public import upper.certificate.SourcePrefixes
public import upper.certificate.Checks

@[expose] public section

/-! Prefix verification needs only the row widths and visibilities.
An existing based-on certificate supplies every actual base length, so this
checker never decodes base strings merely to recover their lengths. -/
namespace SuperpermutationUpperBound.Native14.Certificate
open Transport

/-- The subtraction is in `Nat` before coercion, exactly as in `Row.charge`. -/
def visiblePrefixCheck (width : Nat) : List Nat → List Int → Int → Bool
  | [], [], _ => true
  | visible :: rest, excess :: excesses, start =>
      decide (excess = start) && visiblePrefixCheck width rest excesses
        (start + 1 - ((width - visible : Nat) : Int))
  | _, _, _ => false

/-- Equality of checkers under an actual per-row width theorem.
No validity, bounded visibility, or full/short-row assumption is needed here. -/
theorem sourcePrefixCheck_eq_visiblePrefixCheck {α : Type} (width : Nat)
    (rs : List (Row α)) (excesses : List Int) (start : Int)
    (hwidth : ∀ r ∈ rs, r.base.length = width) :
    sourcePrefixCheck rs excesses start =
      visiblePrefixCheck width (rs.map Row.visible) excesses start := by
  induction rs generalizing excesses start with
  | nil => cases excesses <;> rfl
  | cons r rs ih =>
      have hr : r.charge = width - r.visible := by
        exact congrArg (fun n => n - r.visible) (hwidth r (by simp))
      have ht : ∀ t ∈ rs, t.base.length = width :=
        fun t h => hwidth t (List.mem_cons_of_mem r h)
      cases excesses with
      | nil => rfl
      | cons e es =>
          simp only [sourcePrefixCheck, List.map_cons, visiblePrefixCheck, hr,
            ih es (start + 1 - ((width - r.visible : Nat) : Int)) ht]

/-- Reuse the already certified alphabet permutations to obtain row widths. -/
theorem sourcePrefixCheck_of_visible {width satellite : Nat}
    {rs : List (Row Nat)} {excesses : List Int} {start : Int}
    (hb : BasedOn (List.range width) satellite rs)
    (hc : visiblePrefixCheck width (rs.map Row.visible) excesses start = true) :
    sourcePrefixCheck rs excesses start = true := by
  rw [sourcePrefixCheck_eq_visiblePrefixCheck width rs excesses start
    (fun r hr => (hb r hr).2.1.length_eq.trans (by simp))]
  exact hc

/-- The visibility projection of the literal source bypasses UTF-8 decoding. -/
theorem decodeRows_visibilities (encoded : List (String × Nat)) (satellite : Nat) :
    ((encoded.map (decodeRow satellite)).map Row.visible) = encoded.map Prod.snd := by
  simp only [List.map_map, Function.comp_def, decodeRow]

/-- Check annotations directly against the visible fields of the authoritative
encoded row list, then recover the original checker statement unchanged. -/
theorem sourcePrefixCheck_of_encoded {width satellite : Nat}
    {encoded : List (String × Nat)} {excesses : List Int} {start : Int}
    (hb : BasedOn (List.range width) satellite (encoded.map (decodeRow satellite)))
    (hc : visiblePrefixCheck width (encoded.map Prod.snd) excesses start = true) :
    sourcePrefixCheck (encoded.map (decodeRow satellite)) excesses start = true := by
  apply sourcePrefixCheck_of_visible hb
  simpa only [decodeRows_visibilities] using hc

/-- A finite prefix fact still concerns an occurrence of the actual source row. -/
theorem visiblePrefix_occurrence {width satellite : Nat}
    {rs : List (Row Nat)} {excesses : List Int}
    (hb : BasedOn (List.range width) satellite rs)
    (hc : visiblePrefixCheck width (rs.map Row.visible) excesses 0 = true)
    (i : Nat) (hi : i < rs.length) :
    ∃ pre post, rs = pre ++ rs[i] :: post ∧ signedExcess pre = excesses.getD i 0 :=
  sourcePrefix_occurrence (sourcePrefixCheck_of_visible hb hc) i hi

end SuperpermutationUpperBound.Native14.Certificate
