/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDot

/-! # Selected weight unit columns in successor coordinates

The unit columns of BE (1.14) are compared at every output block,
including blocks without a predecessor of their own. Their following
induction always has the selected successor and retains every dot power.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem unit_conjugate_power
    {A B : Type*} [Category A] [Preadditive A] [Category B]
    (R : A ⥤ B) {P : B} {W V : A} (h : W = V)
    (η : P ⟶ R.obj V) (d : End V) (n : ℕ) :
    ((η ≫ R.map (eqToHom h.symm)) ≫
        R.map ((show End W from eqToHom h ≫ d ≫ eqToHom h.symm) ^ n)) ≫
      R.map (eqToHom h) = η ≫ R.map (d ^ n) := by
  subst V
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id,
    CategoryTheory.Functor.map_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  (δ : WeightBlocks D Λ x)
local notation "J" => elvBlockAppend D Sc cutoff bound i Λ h δ
local notation "Res" => elvBlockRes D Sc cutoff bound i Λ h δ
local notation "ε" => blockSucc D Λ i h δ

/-- Every selected unit and dot power has its literal successor-content column,
including output blocks with no lower predecessor. -/
theorem elvWeightUnit_dotPower_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ x) (n : ℕ) :
    ((elvWeightUnitApp D Sc cutoff bound i Λ h δ M) ≫
        (Res).map ((show End ((elvInductionComponent D Sc cutoff bound i Λ h ε).obj M) from
          elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M ε) ^ n)) ≫
      (Res).map (eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h δ M)) =
    (BalancedInduction.adjunctionUnit J).app (M δ) ≫
      (Res).map ((show End (BalancedInduction.induced J (M δ)) from
        (elvBlockDot D Sc cutoff bound i Λ h δ).app (D.parity i) (M δ)) ^ n) := by
  rw [elvWeightDotComponent_blockSucc]
  exact unit_conjugate_power (Res).toFunctor
    (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h δ M)
    ((BalancedInduction.adjunctionUnit J).app (M δ))
    ((elvBlockDot D Sc cutoff bound i Λ h δ).app (D.parity i) (M δ)) n

end OddMath.QuiverHecke.ELVOld
