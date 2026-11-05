import OddMath.Diagrams.GradedTensor
import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# Non-vacuity: graded tensor products over a graded ring

`OddMath.Diagrams.GradedTensor.isInternal_part` applied to the Laurent polynomial ring
`ℚ[t, t⁻¹]`, graded by degree, tensored over itself with itself.
-/

open OddMath.Diagrams.GradedTensor

noncomputable section

example :
    DirectSum.IsInternal
      (part (K := ℚ) (R := AddMonoidAlgebra ℚ ℤ) (AddMonoidAlgebra.grade ℚ : ℤ → _)
        (AddMonoidAlgebra.grade ℚ : ℤ → _)) :=
  isInternal_part (AddMonoidAlgebra.grade ℚ : ℤ → _) (AddMonoidAlgebra.grade ℚ : ℤ → _)
    (AddMonoidAlgebra.grade ℚ : ℤ → _)
    (fun ha hm => SetLike.GradedMul.mul_mem ha hm) (fun ha hx => SetLike.GradedMul.mul_mem ha hx)

end
