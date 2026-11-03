/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCapPowers
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixRows
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionCrossComparison

/-! # The selected weight power fields are the finite matrix columns and rows

BE (1.13)–(1.14): retain the literal ordinary unitDotColumn and capDotRow
module maps after applying the selected successor-content coordinate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I)

/-- The common-target selected dot is exactly the given module dot endomorphism. -/
theorem elvContentDotTo_component (β γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff bound β) :
    (elvContentDotTo D Sc cutoff bound i β γ hγ).app (D.parity i) M =
      BalancedInduction.dotEnd (contentAppendTo D Sc cutoff bound β [i] γ hγ)
        (contentAppendTo_supernatural D Sc cutoff bound hγ hγ (by
          simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M := by
  exact inductionTransform_app_self _ _ _ M

variable (Λ : X) {x y : X} (h : x + D.α i = y) (β : WeightBlocks D Λ x)
local notation "J" => elvBlockAppend D Sc cutoff bound i Λ h β
local notation "Res" => elvBlockRes D Sc cutoff bound i Λ h β
local notation "δ" => blockSucc D Λ i h β
/-- The given affine dot between the literal selected successor contents. -/
theorem elvBlockGridDot_supernatural : IsSupernatural k (D.parity i)
    (contentAppendToComponent D Sc cutoff bound
      (elvBlockSucc_content_eq D i Λ h β) (elvBlockSucc_content_eq D i Λ h β)
      (dotE D Sc [i] 0)) :=
  contentAppendTo_supernatural D Sc cutoff bound
    (elvBlockSucc_content_eq D i Λ h β) (elvBlockSucc_content_eq D i Λ h β) (by
      simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)
local notation "hDot" => elvBlockGridDot_supernatural D Sc cutoff bound i Λ h β

/-- Every selected weight unit/Rouquier-power field is the literal given finite unit column. -/
theorem elvWeightUnit_gridColumn_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ x) (n : ℕ) :
    ((elvActionUnit D Sc cutoff bound i Λ h ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n ▷
          elvF D Sc cutoff bound i Λ h).total M β) ≫
      (Res).map (eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M)) =
    BalancedInduction.unitDotColumn J hDot (M β) n := by
  have hU := elvWeightUnitPower_total_comparison D Sc cutoff bound i Λ h β M n
  have hD := elvContentDotTo_component D Sc cutoff bound i β.1 δ.1
    (elvBlockSucc_content_eq D i Λ h β) (M β)
  have hC := congrArg (fun d : End (BalancedInduction.induced J (M β)) =>
    (BalancedInduction.adjunctionUnit J).app (M β) ≫ (Res).map (d ^ n)) hD
  exact hU.trans hC

/-- Every supported selected weight Rouquier-power/cap field is the literal given finite cap row. -/
theorem elvWeightCap_gridRow_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ y) (n : ℕ) :
    ((elvF D Sc cutoff bound i Λ h ◁
        SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n ≫
        elvActionCounit D Sc cutoff bound i Λ h).total M δ) =
    eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β
      ((elvF D Sc cutoff bound i Λ h).obj M)) ≫
      BalancedInduction.capDotRow J hDot (M δ) n := by
  have hC := elvWeightCapPower_total_comparison D Sc cutoff bound i Λ h β M n
  have hD := elvContentDotTo_component D Sc cutoff bound i β.1 δ.1
    (elvBlockSucc_content_eq D i Λ h β) ((Res).obj (M δ))
  have hR := congrArg (fun d : End (BalancedInduction.induced J ((Res).obj (M δ))) =>
    eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β
      ((elvF D Sc cutoff bound i Λ h).obj M)) ≫
        (d ^ n) ≫ (BalancedInduction.adjunctionCounit J).app (M δ)) hD
  exact hC.trans hR

end OddMath.QuiverHecke.ELVOld
