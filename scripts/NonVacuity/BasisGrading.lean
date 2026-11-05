import OddMath.Diagrams.BasisGrading
import Mathlib.Algebra.MonoidAlgebra.Grading

/-!
# Non-vacuity: free modules over a graded ring

`OddMath.Diagrams.BasisGrading.isInternal_basisPart` for the free module `ℚ[t, t⁻¹]^(2)` over the
Laurent polynomial ring graded by degree, with basis vectors in degrees `0` and `3`.
-/

open OddMath.Diagrams.BasisGrading

noncomputable section

example :
    DirectSum.IsInternal
      (basisPart (K := ℚ) (AddMonoidAlgebra.grade ℚ : ℤ → _) (![0, 3] : Fin 2 → ℤ)
        (Module.Basis.ofRepr (LinearEquiv.refl (AddMonoidAlgebra ℚ ℤ) (Fin 2 →₀ AddMonoidAlgebra ℚ ℤ)))) :=
  isInternal_basisPart _ _ _

end
