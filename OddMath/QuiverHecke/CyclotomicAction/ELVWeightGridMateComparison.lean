/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightNormalizedMateComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVNormalizedGridMate

/-! # The selected weight Rouquier principal field in grid coordinates

BE (1.13)–(1.14): the negative normalized equal-colour crossing gives
precisely the ordinary grid mate used by the prescribed finite matrices.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₀)
local notation "δ" => blockSucc D Λ i h₁ β
local notation "ε" => blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)
local notation "J" => elvBlockAppend D Sc cutoff bound i Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff bound i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "hGrid" => contentTargetsGridCross_supernatural D Sc cutoff bound
  (Subtype.val β) (Subtype.val (blockSucc D Λ i h₁ β))
  (Subtype.val (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β))) i
  (elvBlockSucc_content_eq D i Λ h₁ β)
  (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ i h₁ β))
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff bound i Λ h₁)
  (elvActionAdjunction D Sc cutoff bound i Λ h₂)
  (elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂)

/-- The prescribed rank-one principal field is the given grid matrix mate
in the selected content source and target coordinates. -/
theorem elvWeightRouquierGridMate_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ x₁) :
    (φ).app (D.parity i) M δ ≫
      eqToHom (elvWeightMixedTarget_obj D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ β M) =
    eqToHom (elvWeightMixedSource_obj D Sc cutoff bound i i Λ h₁ h₁ β M) ≫
      BalancedInduction.orderedGridMateComponent J K hGrid (M δ) := by
  have h := elvWeightRouquierMate_comparison D Sc cutoff bound Λ i h₁ h₂ β M
  have hg := normalizedContentTargetsMate_eq_grid D Sc cutoff bound β.1 δ.1 ε.1 i
    (elvBlockSucc_content_eq D i Λ h₁ β)
    (elvBlockSucc_content_eq D i Λ h₂ δ) (M δ)
  exact h.trans (congrArg (fun f =>
    eqToHom (elvWeightMixedSource_obj D Sc cutoff bound i i Λ h₁ h₁ β M) ≫ f) hg)

end OddMath.QuiverHecke.ELVOld
