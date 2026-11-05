/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirBoundaryDegreeOver
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirClosureIdeal
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirBoundaryIdeal

/-! # The chosen reservoir contractions in the content coefficient ideal over a graded base

SwappedHomInversion §4, condition (J), over a commutative `K`-algebra `R` graded by `𝒜` in
degrees `0, …, b`. The chosen principal closures and the off-window finite boundaries act
through source coefficients of strictly positive degree in the truncated quotient over `K`, so
their post-whiskering actions, with arbitrary morphisms on either side and after native
Hom-sector charts, lie in level one of the jointly nilpotent coefficient ideal
`ELVOld.contentModuleCoefficientIdealOver`
(`ReservoirClosures.positiveNativeClosure_evaluate_memOver`,
`ReservoirClosures.negativeNativeClosure_evaluate_memOver`,
`ReservoirBoundaries.positiveNativeBoundary_evaluate_memOver`,
`ReservoirBoundaries.negativeNativeBoundary_evaluate_memOver`).

For `K = R` with the trivial grading these are the statements of
`OddMath.QuiverHecke.CyclotomicAction.ELVReservoirClosureIdeal` and
`OddMath.QuiverHecke.CyclotomicAction.ELVReservoirBoundaryIdeal`.
-/

noncomputable section

open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.ELVOld

open SwappedAssembly CyclotomicAction

universe u

local instance reservoirIdealOverHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₁)

namespace ReservoirClosures

/-- The positive closure belongs to the source coefficient grading over a graded base. -/
theorem positiveContent_mem_coeffGradingOver (hh : 0 ≤ D.h i x₁) (r s : ℕ) :
    positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s ∈
      (contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1).deg
        (2 * sy.d i * (r + s + 1 : ℕ)) :=
  ⟨positiveCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s,
    positiveCoefficient_mem_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff h₁ h₂ β hh r s,
    ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _⟩

/-- The negative closure has the same coefficient degree over a graded base. -/
theorem negativeContent_mem_coeffGradingOver (hh : D.h i x₁ ≤ 0) (r s : ℕ) :
    negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s ∈
      (contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1).deg
        (2 * sy.d i * (r + s + 1 : ℕ)) :=
  ⟨negativeCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s,
    negativeCoefficient_mem_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff h₁ h₂ β hh r s,
    ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _⟩

variable [Finite I] (b : ℤ) (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (T : PiSCat R)

/-- Arbitrary Hom-sector morphisms may surround the positive closure, over a graded base. -/
theorem positiveContent_sandwich_memOver (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1}
    (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s) ≫ c) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1)
    (m := 2 * sy.d i * (r + s + 1 : ℕ))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r + s + 1 : ℕ) := by positivity
    have hd : (0 : ℤ) < 2 * sy.d i * (r + s + 1 : ℕ) := by positivity
    omega
  · exact positiveContent_mem_coeffGradingOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β hh r s

/-- Arbitrary Hom-sector morphisms may surround the negative closure, over a graded base. -/
theorem negativeContent_sandwich_memOver (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1}
    (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s) ≫ c) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1)
    (m := 2 * sy.d i * (r + s + 1 : ℕ))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r + s + 1 : ℕ) := by positivity
    have hd : (0 : ℤ) < 2 * sy.d i * (r + s + 1 : ℕ) := by positivity
    omega
  · exact negativeContent_mem_coeffGradingOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β hh r s

/-- The whole-weight positive closure action, projected to one output content and surrounded
by arbitrary transformations, lies in the coefficient ideal over a graded base. -/
theorem positiveAction_evaluate_memOver (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z
          (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact positiveContent_sandwich_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 T hh
    r s (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight c (elvBlockEval D Sc cutoff N Λ β))

/-- The whole-weight negative closure action, projected to one output content and surrounded
by arbitrary transformations, lies in the coefficient ideal over a graded base. -/
theorem negativeAction_evaluate_memOver (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z
          (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact negativeContent_sandwich_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 T hh
    r s (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight c (elvBlockEval D Sc cutoff N Λ β))

local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The native positive principal contraction, after output projection and arbitrary
surrounding maps, lies in the coefficient ideal over a graded base. -/
theorem positiveNativeClosure_evaluate_memOver
    (TF : X → PiSCat.{u,u,u + 1} R) (betaP : I →₀ ℕ) (muP : X)
    (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 (TF (-muP))).mem 1
      (Superfunctor.whiskerRight
        (a ≫ (SKM.homContentPostCup TF W i betaP muP h₂ r Z ≫
          (SKM.homContentPostInvPos TF W i betaP muP h₁ h₂ hh Z).f' ≫
          SKM.homContentPostCap TF W i betaP muP h₁ s Z) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCapInverse_closure TF W i betaP muP h₁ h₂ hh Z r s]
  simpa only [positive, Category.assoc] using
    positiveAction_evaluate_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 (TF (-muP))
      hh r s a c

/-- The native negative principal contraction, after output projection and arbitrary
surrounding maps, lies in the coefficient ideal over a graded base. -/
theorem negativeNativeClosure_evaluate_memOver
    (TF : X → PiSCat.{u,u,u + 1} R) (betaP : I →₀ ℕ) (muP : X)
    (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 (TF (-muP))).mem 1
      (Superfunctor.whiskerRight
        (a ≫ (SKM.homContentPostCup TF W i betaP muP h₂ r Z ≫
          (SKM.homContentPostInvNeg TF W i betaP muP h₁ h₂ hh Z).f' ≫
          SKM.homContentPostCap TF W i betaP muP h₁ s Z) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCupInverse_closure TF W i betaP muP h₁ h₂ hh Z r s]
  simpa only [negative, Category.assoc] using
    negativeAction_evaluate_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 (TF (-muP))
      hh r s a c

end ReservoirClosures

namespace ReservoirBoundaries

/-- The positive finite-window boundary has its difference degree over a graded base. -/
theorem positiveContent_mem_coeffGradingOver (hh : 0 ≤ D.h i x₁) (j r : ℕ)
    (hj : j < (D.h i x₁).toNat) :
    positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh j r ∈
      (contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1).deg
        (2 * sy.d i * ((r : ℤ) - j)) :=
  ⟨positiveCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh j r,
    positiveCoefficient_mem_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff h₁ h₂ β hh j r hj,
    ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _⟩

/-- The negative finite-window boundary has its difference degree over a graded base. -/
theorem negativeContent_mem_coeffGradingOver (hh : D.h i x₁ ≤ 0) (j r : ℕ)
    (hj : j < (-D.h i x₁).toNat) :
    negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r j ∈
      (contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1).deg
        (2 * sy.d i * ((r : ℤ) - j)) :=
  ⟨negativeCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r j,
    negativeCoefficient_mem_degreeOver D sy 𝒜 Sc hP cutoff N i Λ hcutoff h₁ h₂ β hh r j hj,
    ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _⟩

variable [Finite I] (b : ℤ) (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (T : PiSCat R)

/-- Arbitrary transformations can surround the positive off-window coefficient, over a graded
base. -/
theorem positiveContent_sandwich_memOver (hh : 0 ≤ D.h i x₁) (j r : ℕ)
    (hj : j < (D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1} (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh j r) ≫ c) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1)
    (m := 2 * sy.d i * ((r : ℤ) - j))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r : ℤ) - j := by omega
    have hd : (0 : ℤ) < 2 * sy.d i * ((r : ℤ) - j) := by positivity
    omega
  · exact positiveContent_mem_coeffGradingOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β hh j r
      hj

/-- Arbitrary transformations can surround the negative off-window coefficient, over a graded
base. -/
theorem negativeContent_sandwich_memOver (hh : D.h i x₁ ≤ 0) (j r : ℕ)
    (hj : j < (-D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1} (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r j) ≫ c) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGradingOver D sy 𝒜 Sc hP cutoff N β.1)
    (m := 2 * sy.d i * ((r : ℤ) - j))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r : ℤ) - j := by omega
    have hd : (0 : ℤ) < 2 * sy.d i * ((r : ℤ) - j) := by positivity
    omega
  · exact negativeContent_mem_coeffGradingOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β hh j r
      hj

/-- The projected positive off-window action lies in the coefficient ideal over a graded
base. -/
theorem positiveAction_evaluate_memOver (hh : 0 ≤ D.h i x₁) (j r : ℕ)
    (hj : j < (D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z
          (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh j r) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact positiveContent_sandwich_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 T hh
    j r hj hjr (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight c (elvBlockEval D Sc cutoff N Λ β))

/-- The projected negative off-window action lies in the coefficient ideal over a graded
base. -/
theorem negativeAction_evaluate_memOver (hh : D.h i x₁ ≤ 0) (j r : ℕ)
    (hj : j < (-D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z
          (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact negativeContent_sandwich_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 T hh
    j r hj hjr (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight c (elvBlockEval D Sc cutoff N Λ β))

local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The native positive off-window contraction has the same ideal membership over a graded
base. -/
theorem positiveNativeBoundary_evaluate_memOver
    (TF : X → PiSCat.{u,u,u + 1} R) (betaP : I →₀ ℕ) (muP : X)
    (hh : 0 ≤ D.h i x₁) (j r : ℕ) (hj : j < (D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 (TF (-muP))).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ((SKM.homContentPostInvPos TF W i betaP muP h₁ h₂ hh Z).g' j ≫
          SKM.homContentPostCap TF W i betaP muP h₁ r Z) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCapInverse_boundary TF W i betaP muP h₁ h₂ hh Z j r]
  simpa only [positive] using
    positiveAction_evaluate_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 (TF (-muP))
      hh j r hj hjr a c

/-- The native negative off-window contraction has the same ideal membership over a graded
base. -/
theorem negativeNativeBoundary_evaluate_memOver
    (TF : X → PiSCat.{u,u,u + 1} R) (betaP : I →₀ ℕ) (muP : X)
    (hh : D.h i x₁ ≤ 0) (j r : ℕ) (hj : j < (-D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (c : Z ⟶ Y) :
    (contentModuleCoefficientIdealOver D sy 𝒜 Sc hP cutoff N β.1 b h𝒜 (TF (-muP))).mem 1
      (Superfunctor.whiskerRight
        (a ≫ (SKM.homContentPostCup TF W i betaP muP h₂ r Z ≫
          (SKM.homContentPostInvNeg TF W i betaP muP h₁ h₂ hh Z).g' j) ≫ c)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCupInverse_boundary TF W i betaP muP h₁ h₂ hh Z r j]
  simpa only [negative] using
    negativeAction_evaluate_memOver D sy 𝒜 Sc hP cutoff N Λ hcutoff i h₁ h₂ β b h𝒜 (TF (-muP))
      hh j r hj hjr a c

end ReservoirBoundaries

end OddMath.QuiverHecke.ELVOld
