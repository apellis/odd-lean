/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSupportedLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightLocalCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMatrixHeight

/-! # Prescribed weight inverses on supported blocks

BE (1.13)–(1.14): transport the constructed supported-content inverse
through the selected weight mate coordinates. The same equations govern
the literal unit/power columns and cap/power rows. Standing cutoff
compatibility identifies every content count with categorical height.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff N Λ x₁)
local notation "δ" => blockSucc D Λ i h₁ β
local notation "ε" => blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)
local notation "J" => elvBlockAppend D Sc cutoff N i Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff N i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "hCross" => contentTargetsGridCross_supernatural D Sc cutoff N
  (Subtype.val β) (Subtype.val (blockSucc D Λ i h₁ β))
  (Subtype.val (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β))) i
  (elvBlockSucc_content_eq D i Λ h₁ β)
  (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ i h₁ β))
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
local notation "hSource" => elvWeightMixedSource_obj D Sc cutoff N i i Λ h₁ h₁ β M
local notation "hTarget" => elvWeightMixedTarget_obj D Sc cutoff N i i Λ h₁ h₂ h₁ h₂ β M

/-- The supported nonpositive-height block has the prescribed weight unit inverse. -/
theorem elvWeightSupportedUnitInverse_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (hh : D.h i x₁ ≤ 0) :
    Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷
          elvF D Sc cutoff N i Λ h₂).total M δ)
      (D.parity i) (fun n => n • D.parity i) (-D.h i x₁).toNat) := by
  rw [← contentUnitCount_weightBlock D cutoff i Λ x₁ hcutoff δ]
  have hc : 0 ≤ contentCrossingHeight D cutoff i δ.1 := by
    rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x₁ hcutoff δ]
    exact neg_nonneg.mpr hh
  let B := Classical.choice (contentTargetsLocalInverseFrom_nonempty D Sc cutoff N β.1 i δ.1 ε.1
    (elvBlockSucc_content_eq D i Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₂ δ) (M δ) hc)
  let a := eqToIso hTarget
  let b := eqToIso hSource
  let c := Iso.refl (M δ)
  have hc0 : c.hom = 𝟙 (M δ) := rfl
  have H := B.mapCoordinates (𝟭 (ContentModules D Sc cutoff N δ.1)) a b c
    (eqToHom_mem_parity_zero hTarget) (eqToHom_mem_parity_zero hSource) (id_mem _)
  have hf : b.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (orderedGridMateComponent J K hCross (M δ)) ≫ a.inv = (φ).app (D.parity i) M δ := by
    have hp := elvWeightRouquierGridMate_comparison D Sc cutoff N i Λ h₁ h₂ β M
    have hs : (φ).app (D.parity i) M δ ≫ a.hom =
        b.hom ≫ orderedGridMateComponent J K hCross (M δ) := by
      simpa only [a, b, eqToIso.hom] using hp
    simpa only [Functor.id_map, ← Category.assoc] using
      (Iso.comp_inv_eq a).2 hs.symm
  have hg (n : ℕ) : c.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (unitDotColumn K (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ δ) (M δ) n) ≫ a.inv =
      (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷
          elvF D Sc cutoff N i Λ h₂).total M δ := by
    have hp := elvWeightUnitPower_localCoordinates D Sc cutoff N i Λ h₁ h₂ β M n
    have hs : (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷
          elvF D Sc cutoff N i Λ h₂).total M δ ≫ a.hom =
        c.hom ≫ unitDotColumn K (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ δ) (M δ) n := by
      simpa only [a, eqToIso.hom, hc0, Category.id_comp] using hp
    simpa only [Functor.id_map, ← Category.assoc] using
      (Iso.comp_inv_eq a).2 hs.symm
  exact ⟨by simpa only [hf, hg] using H⟩

/-- The supported nonnegative-height block has the prescribed weight cap inverse. -/
theorem elvWeightSupportedCapInverse_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (hh : 0 ≤ D.h i x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (elvF D Sc cutoff N i Λ h₁ ◁
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
          elvActionCounit D Sc cutoff N i Λ h₁).total M δ)
      (D.parity i) (fun n => n • D.parity i) (D.h i x₁).toNat) := by
  rw [← contentCapCount_weightBlock D cutoff i Λ x₁ hcutoff δ]
  have hc : contentCrossingHeight D cutoff i δ.1 ≤ 0 := by
    rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x₁ hcutoff δ]
    exact neg_nonpos.mpr hh
  let B := Classical.choice (contentTargetsLocalInverseTo_nonempty D Sc cutoff N β.1 i δ.1 ε.1
    (elvBlockSucc_content_eq D i Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₂ δ) (M δ) hc)
  let a := eqToIso hSource
  let b := eqToIso hTarget
  let c := Iso.refl (M δ)
  have hc0 : c.inv = 𝟙 (M δ) := rfl
  have H := B.mapCoordinates (𝟭 (ContentModules D Sc cutoff N δ.1)) a b c
    (eqToHom_mem_parity_zero hSource) (eqToHom_mem_parity_zero hTarget) (id_mem _)
  have hf : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (orderedGridMateComponent J K hCross (M δ)) ≫ b.inv = (φ).app (D.parity i) M δ := by
    have hp := elvWeightRouquierGridMate_comparison D Sc cutoff N i Λ h₁ h₂ β M
    have hs : (φ).app (D.parity i) M δ ≫ b.hom =
        a.hom ≫ orderedGridMateComponent J K hCross (M δ) := by
      simpa only [a, b, eqToIso.hom] using hp
    simpa only [Functor.id_map, ← Category.assoc] using
      (Iso.comp_inv_eq b).2 hs.symm
  have hg (n : ℕ) : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n) ≫ c.inv =
      (elvF D Sc cutoff N i Λ h₁ ◁
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
          elvActionCounit D Sc cutoff N i Λ h₁).total M δ := by
    have hs : (elvF D Sc cutoff N i Λ h₁ ◁
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
          elvActionCounit D Sc cutoff N i Λ h₁).total M δ =
        a.hom ≫ capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n := by
      simpa only [a, eqToIso.hom] using
        elvWeightCapPower_localCoordinates D Sc cutoff N i Λ h₁ β M n
    rw [Functor.id_map]
    calc
      a.hom ≫ capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n ≫ c.inv =
          (a.hom ≫ capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n) ≫ c.inv :=
        (Category.assoc _ _ _).symm
      _ = a.hom ≫ capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n := by
        rw [hc0]
        exact Category.comp_id _
      _ = _ := hs.symm
  exact ⟨by simpa only [hf, hg] using H⟩

end OddMath.QuiverHecke.ELVOld
