import OddMath
import NonVacuity.EvenNondegeneracy

/-! Non-vacuity checks in `NonVacuity.VacuumRouteEvenComparison`: the all-even comparison for
the vacuum route on the purely even datum of `sl₂`, with every hypothesis proved, over `ℚ` and
over `ℤ`. Conventions are in `scripts/NonVacuity.lean`. -/

noncomputable section

namespace NonVacuity.VacuumRouteEvenComparison

open OddMath.SKM OddMath.SKM.EvenBridge OddMath.QuiverHecke NonVacuity.EvenNondegeneracy

example : Nonempty (Symmetrizer TwoStrandShiftConsumer.datum) ∧ (klScalars ℚ).Homogeneous :=
  vacuumRouteScope_of_isEven cartanSl2 compatible (isKLScalars ℚ)

example : NondegeneracyConjecture (klCScalars ℚ) :=
  vacuumRoute_conclusion_of_isEven cartanSl2 compatible isEven (isKLScalars ℚ) (klCScalars ℚ)

example : NondegeneracyConjecture (klCScalars ℤ) :=
  vacuumRoute_conclusion_of_isEven cartanSl2 compatible isEven (isKLScalars ℤ) (klCScalars ℤ)

end NonVacuity.VacuumRouteEvenComparison
