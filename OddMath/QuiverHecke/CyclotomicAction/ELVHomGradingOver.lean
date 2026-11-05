/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleCoefficientGradedBase
import OddMath.Diagrams.SuperalgebraGradedBase
import OddMath.Diagrams.CoefficientGradedSupercategory
import OddMath.QuiverHecke.CoefficientGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientCategory

/-!
# Integer grading of the ELV coefficient category over a graded base ring

Let `R` be a commutative `K`-algebra graded by `𝒜 : ℤ → Submodule K R`, and let `Sc` be a
parameter system over `R` whose quiver Hecke presentation is coefficient-graded homogeneous
(for instance the truncated Rees parameters, `QuiverHecke.isHomogeneous_truncatedRees`). The
ELV coefficient category over `R` is the box product over `R` of the one-object category of the
ELV coefficient algebra with the quiver Hecke category. Both factors are graded supercategories
over `K` with compatible base-ring degrees, so the box product is one
(`QuiverHecke.elvHomGradingOver`).

For `K = R` with the trivial grading this is the shape of `QuiverHecke.elvHomGrading`; over the
truncated Rees rings it is the ELV grading of `docs/Nondegeneracy/Phase2Plan.md`, step 2.
-/

noncomputable section

open CategoryTheory StringDiagrams OddMath.Diagrams

namespace OddMath.QuiverHecke

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ)

/-- The coefficient factor: the one-object category of the ELV coefficient algebra over `R`,
graded over `K` by the coefficientwise degree. -/
@[instance_reducible]
def elvCoefficientCategoryGradingOver :
    letI := Linear.restrictScalars K R
      (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
    letI := Supercategory.restrictScalars K R
      (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
    GradedSupercategory K (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff)) :=
  letI := SKM.SYM.elvCoefficientDegreeGradedAlgebraOver D sy 𝒜 cutoff
  SuperalgebraCatOver.gradedSupercategory _ (SKM.SYM.elvCoefficientDegreeOver D sy 𝒜 cutoff)
    (fun p hx => SKM.SYM.elvCoefficientDegreeOver_parity cutoff p hx)

/-- The quiver Hecke factor, graded over `K`. -/
@[instance_reducible]
def quiverHeckeGradingOver :
    letI := Linear.restrictScalars K R (H D Sc)
    letI := Supercategory.restrictScalars K R (H D Sc)
    GradedSupercategory K (H D Sc) :=
  CoefficientGrading.gradedSupercategory (isParityHomogeneous D Sc) hP

/-- **Integer grading of the ELV coefficient category over a graded base.** -/
@[instance_reducible]
def elvHomGradingOver :
    letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    GradedSupercategory K (ELVCoefficientCategory D Sc cutoff) :=
  letI := Linear.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  letI := Supercategory.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  haveI : ∀ A B : SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff),
      IsScalarTower K R (A ⟶ B) :=
    Linear.isScalarTower_restrictScalars K R _
  letI := elvCoefficientCategoryGradingOver D sy 𝒜 cutoff
  letI := Linear.restrictScalars K R (H D Sc)
  letI := Supercategory.restrictScalars K R (H D Sc)
  letI := quiverHeckeGradingOver D sy 𝒜 Sc hP
  BoxProdCoefficient.gradedSupercategory (𝒜 := 𝒜)
    (fun {_ _ _ _ _ _} hr hf => by
      change SuperalgebraCat.toElem (_ • _) ∈ SKM.SYM.elvCoefficientDegreeOver D sy 𝒜 cutoff _
      rw [SuperalgebraCat.toElem_smul]
      exact SKM.SYM.smul_mem_elvCoefficientDegreeOver cutoff hr hf)
    (fun {_ _ _ _ _ _} hr hf => CoefficientGrading.smul_mem_presentedPart_add hr hf)
    (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)

end OddMath.QuiverHecke
