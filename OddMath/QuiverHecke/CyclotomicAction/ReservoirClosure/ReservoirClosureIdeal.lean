import OddMath.QuiverHecke.CyclotomicAction.ReservoirClosure.ReservoirClosures

/-!
# Reservoir closure

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The chosen reservoir closures in the content coefficient ideal

SwappedHomInversion §4, condition (J): the literal chosen principal
closures act through positive-degree source coefficients at each exact
content. Their post-whiskering actions, with arbitrary morphisms on either
side, therefore lie in the jointly nilpotent first coefficient level.
The bound is contentwise; no whole-weight nilpotence bound is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.ReservoirClosures
open SwappedAssembly CyclotomicAction
universe u
local instance closureIdealHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₁) (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The entire positive closure belongs to the source coefficient grading. -/
theorem positiveContent_mem_coeffGrading (hh : 0 ≤ D.h i x₁) (r s : ℕ) :
    positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s ∈
      (contentModuleCoeffGrading D Sc cutoff N β.1 sy hc).deg
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  refine ⟨positiveCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s,
    positiveCoefficient_mem_degree D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh r s, ?_⟩
  exact ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _

/-- The negative closure has the same positive coefficient degree. -/
theorem negativeContent_mem_coeffGrading (hh : D.h i x₁ ≤ 0) (r s : ℕ) :
    negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s ∈
      (contentModuleCoeffGrading D Sc cutoff N β.1 sy hc).deg
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  refine ⟨negativeCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s,
    negativeCoefficient_mem_degree D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh r s, ?_⟩
  exact ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _

variable [Finite I] (T : PiSCat k)

/-- Arbitrary Hom-sector morphisms may surround the positive closure. -/
theorem positiveContent_sandwich_mem (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1}
    (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s) ≫ b) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGrading D Sc cutoff N β.1 sy hc)
    (m := 2 * sy.d i * (r + s + 1 : ℕ))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r + s + 1 : ℕ) := by positivity
    have hd : (0 : ℤ) < 2 * sy.d i * (r + s + 1 : ℕ) := by positivity
    omega
  · exact positiveContent_mem_coeffGrading D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh r s

/-- Arbitrary Hom-sector morphisms may surround the negative closure. -/
theorem negativeContent_sandwich_mem (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1}
    (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s) ≫ b) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGrading D Sc cutoff N β.1 sy hc)
    (m := 2 * sy.d i * (r + s + 1 : ℕ))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r + s + 1 : ℕ) := by positivity
    have hd : (0 : ℤ) < 2 * sy.d i * (r + s + 1 : ℕ) := by positivity
    omega
  · exact negativeContent_mem_coeffGrading D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh r s

/-- Projection of the chosen whole-weight positive closure action lies in the
content coefficient ideal, with arbitrary surrounding transformations. -/
theorem positiveAction_evaluate_mem (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z
          (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact positiveContent_sandwich_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc T hh r s
    (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight b (elvBlockEval D Sc cutoff N Λ β))

/-- Projection of the chosen whole-weight negative closure action lies in the
content coefficient ideal, with arbitrary surrounding transformations. -/
theorem negativeAction_evaluate_mem (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z
          (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact negativeContent_sandwich_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc T hh r s
    (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight b (elvBlockEval D Sc cutoff N Λ β))

local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The literal native positive principal contraction, after output
projection and arbitrary surrounding maps, belongs to the content ideal. -/
theorem positiveClosure_evaluate_mem
    (TF : X → PiSCat.{u,u,u + 1} k) (betaP : I →₀ ℕ) (muP : X)
    (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc (TF (-muP))).mem 1
      (Superfunctor.whiskerRight
        (a ≫ (SKM.homContentPostCup TF W i betaP muP h₂ r Z ≫
          (SKM.homContentPostInvPos TF W i betaP muP h₁ h₂ hh Z).f' ≫
          SKM.homContentPostCap TF W i betaP muP h₁ s Z) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCapInverse_closure TF W i betaP muP h₁ h₂ hh Z r s]
  simpa only [positive, Category.assoc] using
    positiveAction_evaluate_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc (TF (-muP)) hh r s a b

/-- The literal native negative principal contraction, after output
projection and arbitrary surrounding maps, belongs to the content ideal. -/
theorem negativeClosure_evaluate_mem
    (TF : X → PiSCat.{u,u,u + 1} k) (betaP : I →₀ ℕ) (muP : X)
    (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc (TF (-muP))).mem 1
      (Superfunctor.whiskerRight
        (a ≫ (SKM.homContentPostCup TF W i betaP muP h₂ r Z ≫
          (SKM.homContentPostInvNeg TF W i betaP muP h₁ h₂ hh Z).f' ≫
          SKM.homContentPostCap TF W i betaP muP h₁ s Z) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCupInverse_closure TF W i betaP muP h₁ h₂ hh Z r s]
  simpa only [negative, Category.assoc] using
    negativeAction_evaluate_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc (TF (-muP)) hh r s a b

end OddMath.QuiverHecke.ELV.ReservoirClosures
end

end

section

/-! # The chosen off-window boundaries in the content coefficient ideal

SwappedHomInversion §4, condition (J): a finite inverse slot j contracted
with a dotted row or column r > j has positive source coefficient degree.
Its exact-content action lies in level one of the jointly nilpotent ideal,
including arbitrary surrounding morphisms and native Hom-sector charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.ReservoirBoundaries
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

end OddMath.QuiverHecke.ELV.ReservoirBoundaries
end

end
