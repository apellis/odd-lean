import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirBoundaryDegree
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCentreWhiskering
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.FactorClosures

/-! # The chosen off-window boundaries in the content coefficient ideal

SwappedHomInversion §4, condition (J): a finite inverse slot j contracted
with a dotted row or column r > j has positive source coefficient degree.
Its exact-content action lies in level one of the jointly nilpotent ideal,
including arbitrary surrounding morphisms and native Hom-sector charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ReservoirBoundaries
open CyclotomicAction SwappedAssembly
universe u
local instance boundaryIdealHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₁) (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The positive chosen finite-window boundary has its difference degree. -/
theorem positiveContent_mem_coeffGrading (hh : 0 ≤ D.h i x₁) (j r : ℕ)
    (hj : j < (D.h i x₁).toNat) :
    positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh j r ∈
      (contentModuleCoeffGrading D Sc cutoff N β.1 sy hc).deg
        (2 * sy.d i * ((r : ℤ) - j)) := by
  refine ⟨positiveCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh j r,
    positiveCoefficient_mem_degree D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh j r hj, ?_⟩
  exact ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _

/-- The negative chosen finite-window boundary has its difference degree. -/
theorem negativeContent_mem_coeffGrading (hh : D.h i x₁ ≤ 0) (j r : ℕ)
    (hj : j < (-D.h i x₁).toNat) :
    negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r j ∈
      (contentModuleCoeffGrading D Sc cutoff N β.1 sy hc).deg
        (2 * sy.d i * ((r : ℤ) - j)) := by
  refine ⟨negativeCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r j,
    negativeCoefficient_mem_degree D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh r j hj, ?_⟩
  exact ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _

variable [Finite I] (T : PiSCat.{u,u,u + 1} k)

/-- Arbitrary transformations can surround the positive off-window coefficient. -/
theorem positiveContent_sandwich_mem (hh : 0 ≤ D.h i x₁) (j r : ℕ)
    (hj : j < (D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1} (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh j r) ≫ b) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGrading D Sc cutoff N β.1 sy hc)
    (m := 2 * sy.d i * ((r : ℤ) - j))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r : ℤ) - j := by omega
    have hd : (0 : ℤ) < 2 * sy.d i * ((r : ℤ) - j) := by positivity
    omega
  · exact positiveContent_mem_coeffGrading D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh j r hj

/-- The projected whole-weight positive off-window action lies in the content ideal. -/
theorem positiveAction_evaluate_mem (hh : 0 ≤ D.h i x₁) (j r : ℕ)
    (hj : j < (D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh j r) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact positiveContent_sandwich_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc T hh j r hj hjr
    (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight b (elvBlockEval D Sc cutoff N Λ β))

/-- Arbitrary transformations can surround the negative off-window coefficient. -/
theorem negativeContent_sandwich_mem (hh : D.h i x₁ ≤ 0) (j r : ℕ)
    (hj : j < (-D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1} (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r j) ≫ b) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGrading D Sc cutoff N β.1 sy hc)
    (m := 2 * sy.d i * ((r : ℤ) - j))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r : ℤ) - j := by omega
    have hd : (0 : ℤ) < 2 * sy.d i * ((r : ℤ) - j) := by positivity
    omega
  · exact negativeContent_mem_coeffGrading D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh j r hj

/-- The projected whole-weight negative off-window action lies in the content ideal. -/
theorem negativeAction_evaluate_mem (hh : D.h i x₁ ≤ 0) (j r : ℕ)
    (hj : j < (-D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact negativeContent_sandwich_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc T hh j r hj hjr
    (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight b (elvBlockEval D Sc cutoff N Λ β))

local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The literal native positive off-window contraction has the same ideal membership. -/
theorem positiveBoundary_evaluate_mem
    (TF : X → PiSCat.{u,u,u + 1} k) (betaP : I →₀ ℕ) (muP : X)
    (hh : 0 ≤ D.h i x₁) (j r : ℕ) (hj : j < (D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc (TF (-muP))).mem 1
      (Superfunctor.whiskerRight (a ≫ ((SKM.homContentPostInvPos TF W i betaP muP h₁ h₂ hh Z).g' j ≫
          SKM.homContentPostCap TF W i betaP muP h₁ r Z) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCapInverse_boundary TF W i betaP muP h₁ h₂ hh Z j r]
  simpa only [positive] using
    positiveAction_evaluate_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc (TF (-muP)) hh j r hj hjr a b

/-- The literal native negative off-window contraction has the same ideal membership. -/
theorem negativeBoundary_evaluate_mem
    (TF : X → PiSCat.{u,u,u + 1} k) (betaP : I →₀ ℕ) (muP : X)
    (hh : D.h i x₁ ≤ 0) (j r : ℕ) (hj : j < (-D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc (TF (-muP))).mem 1
      (Superfunctor.whiskerRight (a ≫ (SKM.homContentPostCup TF W i betaP muP h₂ r Z ≫
          (SKM.homContentPostInvNeg TF W i betaP muP h₁ h₂ hh Z).g' j) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCupInverse_boundary TF W i betaP muP h₁ h₂ hh Z r j]
  simpa only [negative] using
    negativeAction_evaluate_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc (TF (-muP)) hh j r hj hjr a b

end OddMath.QuiverHecke.ELVOld.ReservoirBoundaries
