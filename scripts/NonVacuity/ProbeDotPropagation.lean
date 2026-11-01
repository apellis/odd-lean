import OddMath.QuiverHecke.CyclotomicAction.ProbeDotPropagation

namespace OddMath.ProbeDotPropagationExamples
open QuiverHecke.SignedNilHecke

private def oddU : Matrix (Fin 2) (Fin 2) ℚ := fun i j => if i = j then if i = 0 then 1 else -1 else 0
private def oddV : Matrix (Fin 2) (Fin 2) ℚ := fun i j => if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0
private def oddT : Matrix (Fin 2) (Fin 2) ℚ := fun _ j => if j = 0 then 1/2 else -1/2

private theorem oddRelations : OddTwo oddU oddV oddT := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [oddU, oddV, oddT, Matrix.mul_apply, Fin.sum_univ_two]

private theorem oddU_mul_self : oddU * oddU = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [oddU, Matrix.mul_apply, Fin.sum_univ_two]

/-- A nonzero odd nilHecke representation: the two invertible dots
anticommute and the crossing is square zero. -/
example : Function.Injective (fun x : Matrix (Fin 2) (Fin 2) ℚ => oddV * x) := by
  apply oddRelations.right_mul_injective
  intro x y h
  have hh := congrArg (fun a => oddU * a) h
  simpa only [← mul_assoc, oddU_mul_self, one_mul] using hh

example : IsUnit oddV := by
  apply oddRelations.isUnit_right (k := ℚ)
  exact ⟨⟨oddU, oddU, oddU_mul_self, oddU_mul_self⟩, rfl⟩

private def evenU : Matrix (Fin 2) (Fin 2) ℚ := fun i j => if i = j then if i = 0 then 1 else 2 else 0
private def evenV : Matrix (Fin 2) (Fin 2) ℚ := fun i j => if i = j then if i = 0 then 2 else 1 else 0
private def evenT : Matrix (Fin 2) (Fin 2) ℚ := fun _ j => if j = 0 then -1 else 1
private def evenUInv : Matrix (Fin 2) (Fin 2) ℚ := fun i j => if i = j then if i = 0 then 1 else 1/2 else 0

private theorem evenRelations : EvenTwo evenU evenV evenT := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [evenU, evenV, evenT, Matrix.mul_apply, Fin.sum_univ_two]

private theorem evenUInv_mul : evenUInv * evenU = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [evenU, evenUInv, Matrix.mul_apply, Fin.sum_univ_two]

example : Function.Injective (fun x : Matrix (Fin 2) (Fin 2) ℚ => evenV * x) := by
  apply evenRelations.right_mul_injective
  intro x y h
  have hh := congrArg (fun a => evenUInv * a) h
  simpa only [← mul_assoc, evenUInv_mul, one_mul] using hh

example : IsUnit evenV := by
  apply evenRelations.isUnit_right (k := ℚ)
  refine ⟨⟨evenU, evenUInv, ?_, evenUInv_mul⟩, rfl⟩
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [evenU, evenUInv, Matrix.mul_apply, Fin.sum_univ_two]

example : Function.Injective (fun x : ℚ => (3 : ℚ) * x) := by
  intro x y h
  change (3 : ℚ) * x = 3 * y at h
  apply sub_eq_zero.mp
  apply distinct_dot_kernel (u := (1 : ℚ)) (v := 3) (w := 3) (a := 1)
    (b := 1) (t := 1) (r := 0) 0
  · intro a b hab
    simpa only [one_mul] using hab
  · intro a b hab
    linarith
  · intro a b hab
    simpa only [one_mul] using hab
  · norm_num
  · norm_num
  · simpa only [mul_sub] using sub_eq_zero.mpr h

#print axioms OddMath.QuiverHecke.SignedNilHecke.OddTwo.right_mul_injective
#print axioms OddMath.QuiverHecke.SignedNilHecke.EvenTwo.right_mul_injective
#print axioms OddMath.QuiverHecke.SignedNilHecke.distinct_dot_kernel
#print axioms OddMath.QuiverHecke.SignedNilHecke.OddTwo.isUnit_right
#print axioms OddMath.QuiverHecke.SignedNilHecke.EvenTwo.isUnit_right
end OddMath.ProbeDotPropagationExamples
