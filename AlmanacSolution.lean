import AlmanacDefs
import AlmanacAdapter

/-! The improving asymptotic upper bound. Finite existence corollaries and
explicit words remain in the project; word submissions use a separate form. -/
namespace AlmanacSubmission

/-- S(n) ≤ F₃(n) + (926683/1814400 + o(1))(n-3)!. -/
theorem asymptotic_upper : Almanac.AsymptoticUpper (926683/1814400) :=
  AlmanacAdapter.asymptotic_upper

end AlmanacSubmission
