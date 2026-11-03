/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDot
import OddMath.Algebra.HomogeneousSuperfunctorIso
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
import OddMath.SKM.RouquierData

/-! # Selected weight unit columns in successor coordinates

The unit columns of BE (1.14) are compared at every output block,
including blocks without a predecessor of their own. Their following
induction always has the selected successor and retains every dot power.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem rouquierPower_total
    {k : Type u} [CommRing k] {A B : PiSCat.{u,u,u + 1} k}
    {F : A ⟶ B} (d : F ⟶ F) (n : ℕ) (M : A.carrier) :
    (SKM.rouquierPower d n).total M = (show End (F.obj M) from d.total M) ^ n := by
  induction n with
  | zero => exact SuperNatTrans.id_total F.toFunctor M
  | succ n ih =>
    rw [SKM.rouquierPower, Superfunctor.comp_total, ih, pow_succ', End.mul_def]

private theorem right_whisker_total
    {k : Type u} [CommRing k] {A B E : PiSCat.{u,u,u + 1} k}
    {F G : A ⟶ B} (z : F ⟶ G) (R : B ⟶ E) (M : A.carrier) :
    (z ▷ R).total M = R.map (z.total M) := by
  change R.toFunctor.map (z.app 0 M) + R.toFunctor.map (z.app 1 M) =
    R.toFunctor.map (z.app 0 M + z.app 1 M)
  exact (CategoryTheory.Functor.map_add R.toFunctor).symm

private theorem product_end_power
    {ι : Type*} {V : ι → Type*} [∀ a, Category (V a)]
    {M : ∀ a, V a} (d : End M) (n : ℕ) (a : ι) :
    (d ^ n) a = (show End (M a) from d a) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', End.mul_def, Pi.comp_apply, ih]

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

/-- The selected Rouquier dot powers retain the literal ordinary powers
of the selected dot component in each weight block. -/
theorem elvWeightDotPower_total_component
    (M : ELVWeightProduct D Sc cutoff bound Λ x) (n : ℕ)
    (ζ : WeightBlocks D Λ y) :
    (SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n).total M ζ =
      (show End ((elvInductionComponent D Sc cutoff bound i Λ h ζ).obj M) from
        elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M ζ) ^ n := by
  have hP := rouquierPower_total (elvActionDot D Sc cutoff bound i Λ h) n M
  have hD := HomogeneousSuperfunctorIso.total_eq_app
    (elvActionDot D Sc cutoff bound i Λ h) (elvActionDot_mem D Sc cutoff bound i Λ h) M
  have h := congrFun hP ζ
  rw [product_end_power, hD] at h
  exact h

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

/-- The specified weight unit/Rouquier-power field has exactly the
ordinary content unit/dot column after its selected successor chart. -/
theorem elvWeightUnitPower_total_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ x) (n : ℕ) :
    ((elvActionUnit D Sc cutoff bound i Λ h ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n ▷
          elvF D Sc cutoff bound i Λ h).total M δ) ≫
      (Res).map (eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h δ M)) =
    (BalancedInduction.adjunctionUnit J).app (M δ) ≫
      (Res).map ((show End (BalancedInduction.induced J (M δ)) from
        (elvBlockDot D Sc cutoff bound i Λ h δ).app (D.parity i) (M δ)) ^ n) := by
  have hw := right_whisker_total
    (SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n)
    (elvF D Sc cutoff bound i Λ h) M
  have hc := Superfunctor.comp_total (elvActionUnit D Sc cutoff bound i Λ h)
    (SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n ▷
      elvF D Sc cutoff bound i Λ h) M
  rw [hw] at hc
  have hu : (elvActionUnit D Sc cutoff bound i Λ h).total M =
      (elvWeightUnit D Sc cutoff bound i Λ h).app M := by
    simp only [elvActionUnit, SuperNatTrans.ofNatTrans, SuperNatTrans.total,
      ite_true, one_ne_zero, ite_false, add_zero]
  rw [hu] at hc
  have ha := congrFun hc δ
  dsimp only [elvF, Superfunctor.map, productFunctor, Functor.pi'] at ha
  simp only [Pi.comp_apply] at ha
  have hp := elvWeightDotPower_total_component D Sc cutoff bound i Λ h M n ε
  rw [hp] at ha
  exact (congrArg (fun f => f ≫ (Res).map
    (eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h δ M))) ha).trans
      (elvWeightUnit_dotPower_comparison D Sc cutoff bound i Λ h δ M n)

end OddMath.QuiverHecke.ELVOld
