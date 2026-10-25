import OddMath.QuiverHecke.CyclotomicAction.ExteriorTranslationRelations

/-! Nonzero consumers and an axiom inventory for the local cyclotomic identities.
These consumers do not assert the existence of an SKM action. -/
namespace OddMath.QuiverHecke.CyclotomicAction.Examples
open ExteriorTranslation

/-- Creation plus contraction in the second exterior coordinate. -/
def cliffordDot : ExteriorMatrices :=
  !![0, 0, 1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, -1, 0, 0]

theorem cliffordDot_square : cliffordDot * cliffordDot = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cliffordDot, Matrix.mul_apply, Fin.sum_univ_succ]

theorem cliffordDot_exterior : firstExterior * cliffordDot = -(cliffordDot * firstExterior) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cliffordDot, firstExterior, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The first-dot normalizer acts on a nonzero square and nonzero exterior parameter. -/
theorem matrix_even_normality :
    cliffordDot * (1 - cliffordDot * firstExterior) =
      (1 - cliffordDot * firstExterior) * (cliffordDot - 2 * firstExterior) := by
  simpa [cliffordDot_square] using evenCutoff_normality cliffordDot firstExterior 0 1
    cliffordDot_exterior firstExterior_square (by simp) (by simp) (by simp) (by simp)

theorem matrix_inverse_balance :
    (cliffordDot + 2 * firstExterior) * (1 - cliffordDot * firstExterior) =
      (1 - cliffordDot * firstExterior) * cliffordDot := by
  simpa [cliffordDot_square] using evenCutoff_inverse_balance cliffordDot firstExterior 0 1
    cliffordDot_exterior firstExterior_square (by simp) (by simp) (by simp)

/-- Replacing the inverse normalizer by the normalizer is genuinely false. -/
theorem normalizer_not_inverse_balance :
    (cliffordDot - 2 * firstExterior) * (1 - cliffordDot * firstExterior) ≠
      (1 - cliffordDot * firstExterior) * cliffordDot := by
  intro h
  have he := congrArg (fun m : ExteriorMatrices => m 1 0) h
  norm_num [cliffordDot, firstExterior, Matrix.mul_apply, Matrix.ofNat_apply,
    Fin.sum_univ_succ] at he

/-- Directed signs, unlike a uniform sign, give the required constant square. -/
def directedCrossing : TwoWordAlgebra := !![0, 1; -1, 0]

theorem directedCrossing_square : directedCrossing * directedCrossing = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [directedCrossing, Matrix.mul_apply, Fin.sum_univ_two]

theorem directedCrossing_parity : matrixParity directedCrossing = -directedCrossing := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrixParity, parityMatrix, directedCrossing, Matrix.mul_apply, Fin.sum_univ_two]

/-- A single operator incorporating the two directed signs squares to the identity. -/
theorem directed_operator_square (h : TwoWordAlgebra) :
    oddRight matrixParity directedCrossing (oddRight matrixParity directedCrossing h) = h := by
  rw [oddRight_comp matrixParity matrixParity_involutive directedCrossing directedCrossing
    directedCrossing_parity, directedCrossing_square]
  simp

#print axioms oddRight_comp
#print axioms uniform_crossing_sign_fails
#print axioms evenCutoff_normality
#print axioms evenCutoff_inverse_balance
#print axioms evenCutoff_conjugate
#print axioms oddCutoff_normality
#print axioms oddCutoff_square
#print axioms mixed_dots
#print axioms quadratic_polynomial
#print axioms repeated_outer_braid
#print axioms exterior_product_ne_zero
#print axioms translated_exterior_braid
#print axioms matrix_even_normality
#print axioms matrix_inverse_balance
#print axioms normalizer_not_inverse_balance
#print axioms directed_operator_square

end OddMath.QuiverHecke.CyclotomicAction.Examples
