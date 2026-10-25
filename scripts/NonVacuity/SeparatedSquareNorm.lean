import OddMath.Diagrams.OddNilHecke.SeparatedSquareNorm
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace NonVacuity.SeparatedSquareNorm
open OddMath.OddNilHecke.Intertwiner
def x : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]
def y : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

theorem x_ne_zero : x ≠ 0 := by
  intro h
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 1) h
  norm_num [x] at this

theorem actual_separated_norm :
    IsUnit (-(squareDiff x y ^ 2 * (x ^ 2 + y ^ 2))) := by
  have hx : x ^ 2 = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [x, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hy : y ^ 2 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [y, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hxy : x * y + y * x = 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [x, y, Matrix.mul_apply, Fin.sum_univ_two]
  exact (separated_square_norm_isUnit
    (show IsNilpotent (x ^ 2) from ⟨1, by simp [hx]⟩)
    (hy ▸ isUnit_one) hxy).2.2

#print axioms actual_separated_norm
#print axioms separated_square_norm_isUnit
end NonVacuity.SeparatedSquareNorm
