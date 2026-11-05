/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightGridMateComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightGridPowerComparison

/-! # Common coordinates for prescribed local weight matrix fields

BE (1.13)–(1.14): the unit columns and cap rows use exactly the same
source and target equations as the prescribed Rouquier principal mate.
These whole module-map identities supply the selected chart transport
for the supported weight local inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff N Λ x₁)
local notation "δ" => blockSucc D Λ i h₁ β
local notation "J" => elvBlockAppend D Sc cutoff N i Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff N i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "ResU" => elvBlockRes D Sc cutoff N i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "hSource" => elvWeightMixedSource_obj D Sc cutoff N i i Λ h₁ h₁ β M
local notation "hTarget" => elvWeightMixedTarget_obj D Sc cutoff N i i Λ h₁ h₂ h₁ h₂ β M

/-- The selected principal-target equation is the upper induction equation under restriction. -/
theorem elvWeightLocalTarget_hom :
    eqToHom hTarget = (ResU).map (eqToHom
      (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ δ M)) := by
  exact (eqToHom_map (ResU).toFunctor
    (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ δ M)).symm

/-- The literal unit columns use the very same target chart as the principal mate. -/
theorem elvWeightUnitPower_localCoordinates (n : ℕ) :
    ((elvActionUnit D Sc cutoff N i Λ h₂ ≫
      SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷
        elvF D Sc cutoff N i Λ h₂).total M δ) ≫ eqToHom hTarget =
      unitDotColumn K (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ δ) (M δ) n := by
  have h := congrArg (fun f =>
    ((elvActionUnit D Sc cutoff N i Λ h₂ ≫
      SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷
        elvF D Sc cutoff N i Λ h₂).total M δ) ≫ f)
    (elvWeightLocalTarget_hom D Sc cutoff N i Λ h₁ h₂ β M)
  exact h.trans (elvWeightUnit_gridColumn_comparison D Sc cutoff N i Λ h₂ δ M n)

/-- The literal cap rows use the very same source chart as the principal mate. -/
theorem elvWeightCapPower_localCoordinates (n : ℕ) :
    ((elvF D Sc cutoff N i Λ h₁ ◁
      SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
        elvActionCounit D Sc cutoff N i Λ h₁).total M δ) =
      eqToHom hSource ≫ capDotRow J
        (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n :=
  elvWeightCap_gridRow_comparison D Sc cutoff N i Λ h₁ β M n

end OddMath.QuiverHecke.ELVOld
