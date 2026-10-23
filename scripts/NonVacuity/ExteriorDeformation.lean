import OddMath.Diagrams.OddNilHecke.ExteriorDeformation

/-! A nonzero exterior parameter in the two-strand local cyclotomic model.
This does not assert an SKM action or the Nondegeneracy Conjecture. -/

open OddMath.OddNilHecke.ExteriorDeformation

namespace NonVacuity.ExteriorDeformation

example : exterior dualParameter ≠ 0 := dualNumber_model.1

example :
    exterior dualParameter * firstDot dualParameter +
      firstDot dualParameter * exterior dualParameter = 0 ∧
    exterior dualParameter * secondDot dualParameter +
      secondDot dualParameter * exterior dualParameter = 0 ∧
    exterior dualParameter * crossing + crossing * exterior dualParameter = 0 :=
  exterior_anticommutes _ (TrivSqZeroExt.inr_mul_inr ℚ 1 1)

example :
    crossing (R := TrivSqZeroExt ℚ ℚ) * crossing = 0 ∧
    firstDot dualParameter * secondDot dualParameter +
      secondDot dualParameter * firstDot dualParameter = 0 ∧
    crossing * firstDot dualParameter + secondDot dualParameter * crossing = 1 ∧
    firstDot dualParameter * crossing + crossing * secondDot dualParameter = 1 :=
  nilHecke_relations _

#print axioms nilHecke_relations
#print axioms exterior_anticommutes
#print axioms exterior_square
#print axioms cyclotomic_relation
#print axioms exterior_injective
#print axioms exterior_ne_zero
#print axioms dualNumber_model

end NonVacuity.ExteriorDeformation
