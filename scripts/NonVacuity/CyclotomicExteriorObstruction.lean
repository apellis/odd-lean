import OddMath.Diagrams.OddNilHecke.CyclotomicExteriorObstruction
import OddMath.Diagrams.OddNilHecke.ExteriorDeformation

open OddMath.OddNilHecke
open ExteriorDeformation

-- A concrete nonzero exterior scalar satisfies the obstruction at b=0.
example : exterior dualParameter ≠ 0 ∧
    (2 : Matrix (Fin 2) (Fin 2) (TrivSqZeroExt ℚ ℚ)) * 0 *
      exterior dualParameter = 0 := by
  refine ⟨dualNumber_model.1, ?_⟩
  apply CyclotomicExteriorObstruction.twice_constant_mul_exterior_eq_zero
    (firstDot dualParameter) (exterior dualParameter) 0
  · exact dualNumber_model.2.1
  · apply eq_neg_of_add_eq_zero_left
    exact (exterior_anticommutes dualParameter
      (TrivSqZeroExt.inr_mul_inr ℚ 1 1)).1
  · exact dualNumber_model.2.2
  · simp

#print axioms CyclotomicExteriorObstruction.twice_constant_mul_exterior_eq_zero_of_factor
#print axioms CyclotomicExteriorObstruction.twice_constant_mul_exterior_eq_zero
#print axioms CyclotomicExteriorObstruction.exterior_eq_zero_of_leftInverse
