/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightUnitPowers

/-! # Selected weight cap rows in predecessor coordinates

BE (1.13): the prescribed lower Rouquier dot powers followed by the
selected counit are ordinary content cap rows in the selected supported
source coordinate. Every power and the full input module are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem left_whisker_total
    {k : Type u} [CommRing k] {A B E : PiSCat.{u,u,u + 1} k}
    (F : A ⟶ B) {G H : B ⟶ E} (z : G ⟶ H) (M : A.carrier) :
    (F ◁ z).total M = z.total (F.obj M) := rfl

private theorem conjugate_power_counit
    {A : Type*} [Category A] [Preadditive A]
    {V W Z : A} (h : W = V) (d : End V) (ε : V ⟶ Z) (n : ℕ) :
    ((show End W from eqToHom h ≫ d ≫ eqToHom h.symm) ^ n) ≫
      (eqToHom h ≫ ε) = eqToHom h ≫ (d ^ n) ≫ ε := by
  subst V
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
  (β : WeightBlocks D Λ x)
local notation "J" => elvBlockAppend D Sc cutoff bound i Λ h β
local notation "Res" => elvBlockRes D Sc cutoff bound i Λ h β
local notation "δ" => blockSucc D Λ i h β
local notation "F" => elvF D Sc cutoff bound i Λ h

/-- Every selected ordinary dot power/cap row retains its supported content source. -/
theorem elvWeightCounit_dotPower_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ y) (n : ℕ) :
    ((show End ((elvInductionComponent D Sc cutoff bound i Λ h δ).obj ((F).obj M)) from
      elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) ((F).obj M) δ) ^ n) ≫
      (elvWeightCounit D Sc cutoff bound i Λ h).app M δ =
    eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β ((F).obj M)) ≫
      ((show End (BalancedInduction.induced J ((Res).obj (M δ))) from
        (elvBlockDot D Sc cutoff bound i Λ h β).app (D.parity i) ((Res).obj (M δ))) ^ n) ≫
      (BalancedInduction.adjunctionCounit J).app (M δ) := by
  dsimp only [elvWeightCounit]
  rw [elvWeightDotComponent_blockSucc, elvWeightCounitComponent_blockSucc]
  exact conjugate_power_counit
    (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β ((F).obj M))
    ((elvBlockDot D Sc cutoff bound i Λ h β).app (D.parity i) ((Res).obj (M δ)))
    ((BalancedInduction.adjunctionCounit J).app (M δ)) n

/-- The specified lower Rouquier-power/cap field has the literal content cap row. -/
theorem elvWeightCapPower_total_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ y) (n : ℕ) :
    ((F ◁ SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n ≫
        elvActionCounit D Sc cutoff bound i Λ h).total M δ) =
    eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β ((F).obj M)) ≫
      ((show End (BalancedInduction.induced J ((Res).obj (M δ))) from
        (elvBlockDot D Sc cutoff bound i Λ h β).app (D.parity i) ((Res).obj (M δ))) ^ n) ≫
      (BalancedInduction.adjunctionCounit J).app (M δ) := by
  have hw := left_whisker_total F
    (SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n) M
  have hc := Superfunctor.comp_total
    (F ◁ SKM.rouquierPower (elvActionDot D Sc cutoff bound i Λ h) n)
    (elvActionCounit D Sc cutoff bound i Λ h) M
  rw [hw] at hc
  have hu : (elvActionCounit D Sc cutoff bound i Λ h).total M =
      (elvWeightCounit D Sc cutoff bound i Λ h).app M := by
    simp only [elvActionCounit, SuperNatTrans.ofNatTrans, SuperNatTrans.total,
      ite_true, one_ne_zero, ite_false, add_zero]
  rw [hu] at hc
  have ha := congrFun hc δ
  simp only [Pi.comp_apply] at ha
  rw [elvWeightDotPower_total_component] at ha
  exact ha.trans (elvWeightCounit_dotPower_comparison D Sc cutoff bound i Λ h β M n)

end OddMath.QuiverHecke.ELVOld
