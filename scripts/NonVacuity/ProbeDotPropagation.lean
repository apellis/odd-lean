import OddMath.QuiverHecke.CyclotomicAction.ProbeDotPropagation
import Mathlib.Data.Matrix.Notation

namespace OddMath.ProbeDotPropagationExamples
open QuiverHecke.SignedNilHecke

private def oddU : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]
private def oddV : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; -1, 0]
private def oddT : Matrix (Fin 2) (Fin 2) ℚ := !![1/2, -1/2; 1/2, -1/2]

private theorem oddRelations : OddTwo oddU oddV oddT := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [oddU, oddV, oddT, Matrix.mul_apply, Fin.sum_univ_two]

private theorem oddU_mul_self : oddU * oddU = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [oddU, Matrix.mul_apply, Fin.sum_univ_two]

/-- A nonzero odd nilHecke representation: the two invertible dots
anticommute and the crossing is square zero. -/
example : Function.Injective (fun x : Matrix (Fin 2) (Fin 2) ℚ => oddV * x) := by
  apply oddRelations.right_mul_injective
  intro x y h
  have hh := congrArg (fun a => oddU * a) h
  simpa only [← mul_assoc, oddU_mul_self, one_mul] using hh

private def evenU : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 2]
private def evenV : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 1]
private def evenT : Matrix (Fin 2) (Fin 2) ℚ := !![-1, 1; -1, 1]
private def evenUInv : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 1/2]

private theorem evenRelations : EvenTwo evenU evenV evenT := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [evenU, evenV, evenT, Matrix.mul_apply, Fin.sum_univ_two]

private theorem evenUInv_mul : evenUInv * evenU = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [evenU, evenUInv, Matrix.mul_apply, Fin.sum_univ_two]

example : Function.Injective (fun x : Matrix (Fin 2) (Fin 2) ℚ => evenV * x) := by
  apply evenRelations.right_mul_injective
  intro x y h
  have hh := congrArg (fun a => evenUInv * a) h
  simpa only [← mul_assoc, evenUInv_mul, one_mul] using hh

example : Function.Injective (fun x : ℚ => (3 : ℚ) * x) := by
  intro x y h
  apply sub_eq_zero.mp
  apply distinct_dot_kernel (u := (1 : ℚ)) (w := 3) (a := 1)
    (b := 1) (t := 1) (r := 0) 0
  · simp
  · intro a b hab
    linarith
  · simp
  · norm_num
  · norm_num
  · simpa only [mul_sub] using sub_eq_zero.mpr h

#print axioms OddMath.QuiverHecke.SignedNilHecke.OddTwo.right_mul_injective
#print axioms OddMath.QuiverHecke.SignedNilHecke.EvenTwo.right_mul_injective
#print axioms OddMath.QuiverHecke.SignedNilHecke.distinct_dot_kernel
end OddMath.ProbeDotPropagationExamples
