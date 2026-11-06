import OddMath.QuiverHecke.BWWGrading
import NonVacuity.BWWGradedParameters

/-! # Gradings with Brundan–Wang–Webster parameters

On the datum of `NonVacuity.BWWScalars` with symmetrizer `(1, 1)`: the parameters
`u³ + uv² + v³` satisfy (1.31), so both presentations with these parameters are graded. The coefficient-graded statement is applied to `u³ + v³ + 1`.
-/

noncomputable section
namespace NonVacuity.BWWGrading
open OddMath OddMath.SKM NonVacuity.BWWScalars NonVacuity.BWWGradedParameters

theorem homogeneousBWW : scalars.toBWW.Homogeneous :=
  (ScalarData.toBWW_homogeneous_iff scalars).mpr homogeneous

example : (SKM.presBWW datum scalars.toBWW).IsHomogeneous (SKM.gdeg datum symmetrizer) :=
  SKM.isHomogeneous_gdeg_presBWW datum symmetrizer homogeneousBWW

example : (QuiverHecke.presBWW datum scalars.toBWW).IsHomogeneous
    (QuiverHecke.gdeg datum symmetrizer) :=
  QuiverHecke.isHomogeneous_gdeg_presBWW datum symmetrizer homogeneousBWW

/-- `ℚ` with every element in every degree. -/
def topGrading : ℤ → Submodule ℚ ℚ := fun _ => ⊤

instance : SetLike.GradedMonoid topGrading where
  one_mem := by simp [topGrading]
  mul_mem := by intro _ _ _ _ _ _; simp [topGrading]

/-- The coefficient-graded statement applies to `u³ + v³ + 1`, with its pure monomial. -/
example : OddMath.Diagrams.CoefficientGrading.IsHomogeneous topGrading
    (QuiverHecke.gdeg datum symmetrizer) (QuiverHecke.presBWW datum constantTerm) :=
  QuiverHecke.isHomogeneous_coefficientGraded_presBWW datum symmetrizer topGrading constantTerm
    (fun _ _ => by simp [topGrading]) (fun _ _ _ _ _ _ _ _ => by simp [topGrading])

end NonVacuity.BWWGrading
