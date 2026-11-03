/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAbsentUnitInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightGridPowerComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightLocalMate

/-! # The prescribed weight unit inverse on absent predecessor blocks

BE (1.14): transport the constructed canonical absent-content inverse
to the selected weight mate and the literal upper unit/Rouquier powers.
The source-required cutoff/highest-weight match fixes the finite count.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem singletonDot_mem (i : I) :
    dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1

/-- The absent-content inverse retains an arbitrary stored upper successor. -/
theorem contentAbsentUnitTargetInverse_nonempty (β γ : Multiset I) (i : I)
    (hγ : β + ([i] : Multiset I) = γ) (hi : i ∉ β)
    (M : ContentModules D Sc cutoff N β) :
    Nonempty (SKM.SuperSumInvFrom (k := k)
      (0 : elvZeroModule D Sc cutoff N β ⟶
        (restriction (contentAppendTo D Sc cutoff N β [i] γ hγ)).obj
          (induced (contentAppendTo D Sc cutoff N β [i] γ hγ) M))
      (unitDotColumn (contentAppendTo D Sc cutoff N β [i] γ hγ)
        (contentAppendTo_supernatural D Sc cutoff N hγ hγ (singletonDot_mem D Sc i)) M)
      (D.parity i) (fun n => n • D.parity i) (contentUnitCount D cutoff i β)) := by
  subst γ
  exact contentAbsentUnitInverse_nonempty D Sc cutoff N β i hi M

variable (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (δ : WeightBlocks D Λ x₁)
local notation "K" => elvBlockAppend D Sc cutoff N i Λ h₂ δ
local notation "ResU" => elvBlockRes D Sc cutoff N i Λ h₂ δ
local notation "ε" => blockSucc D Λ i h₂ δ
local notation "E₁" => elvE D Sc cutoff N i Λ h₁
local notation "F₁" => elvF D Sc cutoff N i Λ h₁
local notation "E₂" => elvE D Sc cutoff N i Λ h₂
local notation "F₂" => elvF D Sc cutoff N i Λ h₂
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)

/-- The following F/E object always has its selected upper successor coordinate. -/
theorem elvWeightFollowing_obj (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    ((E₂ ≫ F₂).obj M) δ = (ResU).obj (induced K (M δ)) := by
  change (ResU).obj ((elvInductionComponent D Sc cutoff N i Λ h₂ ε).obj M) = _
  exact congrArg (fun V => (ResU).obj V)
    (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ δ M)

/-- Every absent predecessor block has the prescribed weight local unit inverse,
with the actual Rouquier principal field and upper unit/power fields. -/
theorem elvWeightAbsentUnitInverse_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷ F₂).total M δ)
      (D.parity i) (fun n => n • D.parity i) (-D.h i x₁).toNat) := by
  rw [← contentUnitCount_weightBlock D cutoff i Λ x₁ hcutoff δ]
  refine ⟨?_⟩
  have hi : i ∉ δ.1 := fun hm => hδ ((exists_blockSucc_iff D Λ i h₁ δ).mpr hm)
  let J := Classical.choice (contentAbsentUnitTargetInverse_nonempty D Sc cutoff N δ.1 ε.1 i
    (elvBlockSucc_content_eq D i Λ h₂ δ) hi (M δ))
  let a := eqToIso (elvWeightFollowing_obj D Sc cutoff N i Λ h₂ δ M)
  have hB : Limits.IsZero (((F₁ ≫ E₁).obj M) δ) :=
    elvInductionComponent_isZero D Sc cutoff N i Λ h₁ δ hδ ((F₁).obj M)
  let b := hB.iso (elvZeroModule_isZero D Sc cutoff N δ.1)
  let c := Iso.refl (M δ)
  have hc : c.hom = 𝟙 (M δ) := rfl
  have hb : b.hom ∈ parity (R := k) _ _ 0 := by
    rw [hB.eq_of_src b.hom 0]
    exact Submodule.zero_mem _
  have H := J.mapCoordinates (𝟭 (ContentModules D Sc cutoff N δ.1)) a b c
    (eqToHom_mem_parity_zero (elvWeightFollowing_obj D Sc cutoff N i Λ h₂ δ M)) hb (id_mem _)
  have hf : b.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (0 : elvZeroModule D Sc cutoff N δ.1 ⟶ (ResU).obj (induced K (M δ))) ≫ a.inv =
      (φ).app (D.parity i) M δ := hB.eq_of_src _ _
  have ha : a.hom = (ResU).map
      (eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ δ M)) := by
    exact (eqToHom_map (ResU).toFunctor
      (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ δ M)).symm
  have hg (n : ℕ) : c.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (unitDotColumn K (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ δ) (M δ) n) ≫ a.inv =
      (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷ F₂).total M δ := by
    have hU := elvWeightUnit_gridColumn_comparison D Sc cutoff N i Λ h₂ δ M n
    have hA := congrArg (fun f =>
      (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷ F₂).total M δ ≫ f) ha
    have he := congrArg (fun f => f ≫ a.inv) (hA.trans hU)
    simpa only [hc, Functor.id_map, Category.id_comp, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] using he.symm
  simpa only [hf, hg] using H

end OddMath.QuiverHecke.ELVOld
