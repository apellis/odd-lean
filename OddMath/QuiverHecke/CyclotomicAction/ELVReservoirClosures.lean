import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierFamily
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCentreBlocks

/-! # Exact-content attachment of the chosen reservoir closures

The principal inverse is the field selected by `elvRouquierFamily.loc`.
The comparison with every whole-weight input follows from naturality,
without an independently supplied comparison or a module-Hom grading.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ReservoirClosures
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The literal positive-height chosen cup-dot/principal/dot-cap closure. -/
def positive (hh : 0 ≤ D.h i x₁) (r s : ℕ) :
    End (Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x₁)) :=
  ((W).adj i h₂).unit ≫ SKM.rouquierPower ((W).dot i h₂) r ▷ (W).F i h₂ ≫
    (((W).loc i h₁ h₂).invPos hh).f' ≫
      ((W).F i h₁ ◁ SKM.rouquierPower ((W).dot i h₁) s ≫ ((W).adj i h₁).counit)

/-- The literal negative-height chosen cup-dot/principal/dot-cap closure. -/
def negative (hh : D.h i x₁ ≤ 0) (r s : ℕ) :
    End (Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x₁)) :=
  ((W).adj i h₂).unit ≫ SKM.rouquierPower ((W).dot i h₂) r ▷ (W).F i h₂ ≫
    (((W).loc i h₁ h₂).invNeg hh).f' ≫
      ((W).F i h₁ ◁ SKM.rouquierPower ((W).dot i h₁) s ≫ ((W).adj i h₁).counit)

variable (β : WeightBlocks D Λ x₁)

def positiveContent (hh : 0 ≤ D.h i x₁) (r s : ℕ) : ModuleCentre.Centre D Sc cutoff N β.1 :=
  WeightCentreBlocks.restrict D Sc cutoff N Λ β (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s)
def negativeContent (hh : D.h i x₁ ≤ 0) (r s : ℕ) : ModuleCentre.Centre D Sc cutoff N β.1 :=
  WeightCentreBlocks.restrict D Sc cutoff N Λ β (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s)

/-- Literal whole-weight closure, at its selected output content, on every input. -/
theorem positiveContent_total (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s).total (M β) =
      (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M β :=
  WeightCentreBlocks.restrict_total D Sc cutoff N Λ β _ M

theorem negativeContent_total (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s).total (M β) =
      (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M β :=
  WeightCentreBlocks.restrict_total D Sc cutoff N Λ β _ M

/-- The recovered source coefficient of the actual positive closure. -/
def positiveCoefficient (hh : 0 ≤ D.h i x₁) (r s : ℕ) : ContentCoefficient D Sc cutoff N β.1 :=
  ModuleCentre.reconstruct D Sc cutoff N β.1 (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s)
def negativeCoefficient (hh : D.h i x₁ ≤ 0) (r s : ℕ) : ContentCoefficient D Sc cutoff N β.1 :=
  ModuleCentre.reconstruct D Sc cutoff N β.1 (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s)

end OddMath.QuiverHecke.ELVOld.ReservoirClosures
