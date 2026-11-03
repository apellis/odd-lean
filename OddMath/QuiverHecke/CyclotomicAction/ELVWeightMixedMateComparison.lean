/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightRectangularCross

/-! # Weight cup and cap in rectangular mixed-mate coordinates

The remaining transport for Brundan–Ellis (1.12) compares the selected
weight adjunction maps through the supported content coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem unit_transport
    {k C B : Type u} [CommRing k] [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {P Q : Superfunctor k C (SVec k)} {W : Superfunctor k B (SVec k)}
    (hPQ : P = Q) (hWP : W = BalancedInduction.induced J P)
    (hWQ : W = BalancedInduction.induced J Q) :
    ((BalancedInduction.adjunctionUnit J).app P ≫
      (BalancedInduction.restriction J).map (eqToHom hWP.symm)) ≫
        (BalancedInduction.restriction J).map (eqToHom hWQ) =
      eqToHom hPQ ≫ (BalancedInduction.adjunctionUnit J).app Q := by
  subst Q
  subst W
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  exact Category.comp_id _

private theorem map_counit_transport
    {A E : Type*} [Category* A] [Category* E] (L : A ⥤ E)
    {Y Z T : A} {P Q : E} (hYZ : Y = Z) (hP : P = L.obj Y)
    (hQ : Q = L.obj T) (hPZ : P = L.obj Z) (f : Z ⟶ T) :
    (eqToHom hP ≫ L.map (eqToHom hYZ ≫ f) ≫ eqToHom hQ.symm) ≫ eqToHom hQ =
      eqToHom hPZ ≫ L.map f := by
  subst Z
  subst P
  subst Q
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- The map of induction retains an arbitrary prescribed successor block. -/
theorem elvInductionComponent_map_of (i : I) (Λ : X) {x y : X}
    (h : x + D.α i = y) (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y)
    (hβ : blockSucc D Λ i h β = δ)
    {M N : ELVWeightProduct D Sc cutoff bound Λ x} (f : M ⟶ N) :
    (elvInductionComponent D Sc cutoff bound i Λ h δ).map f =
      eqToHom (elvInductionComponent_obj_of D Sc cutoff bound i Λ h β δ hβ M) ≫
        (BalancedInduction.induction
          (contentAppendTo D Sc cutoff bound β.1 [i] δ.1
            ((elvBlockSucc_content_eq D i Λ h β).trans (congrArg Subtype.val hβ)))).map (f β) ≫
          eqToHom (elvInductionComponent_obj_of D Sc cutoff bound i Λ h β δ hβ N).symm := by
  subst δ
  exact elvInductionComponent_map_blockSucc D Sc cutoff bound i Λ h β f

variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
  (β : WeightBlocks D Λ x₀)
local notation "δj" => blockSucc D Λ j h₁ β
local notation "δi" => blockSucc D Λ i h₃ β
local notation "ε" => blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)
local notation "J" => elvBlockAppend D Sc cutoff bound j Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff bound i Λ h₃ β
local notation "U" => elvBlockAppend D Sc cutoff bound j Λ h₄ (blockSucc D Λ i h₃ β)
local notation "Fj" => elvF D Sc cutoff bound j Λ h₁
local notation "Ei" => elvE D Sc cutoff bound i Λ h₃
local notation "sourcePairEq" => elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound j i Λ h₃ h₄ β
  (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)) rfl

/-- The selected upper weight cup commutes with the supported source and pair coordinates. -/
theorem elvWeightMixedUnit_comparison (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    (elvWeightUnitApp D Sc cutoff bound j Λ h₄ δi ((Ei).obj ((Fj).obj M))) ≫
      (BalancedInduction.restriction U).map
        (eqToHom (congrArg (fun F => CategoryTheory.Functor.obj F ((Fj).obj M)) sourcePairEq)) =
      eqToHom (elvWeightMixedSource_obj D Sc cutoff bound i j Λ h₁ h₃ β M) ≫
        (BalancedInduction.adjunctionUnit U).app
          (BalancedInduction.induced K ((BalancedInduction.restriction J).obj (M δj))) := by
  have h := unit_transport U
    (elvWeightMixedSource_obj D Sc cutoff bound i j Λ h₁ h₃ β M)
    (elvInductionComponent_obj_blockSucc D Sc cutoff bound j Λ h₄ δi ((Ei).obj ((Fj).obj M)))
    (congrArg (fun F => CategoryTheory.Functor.obj F ((Fj).obj M)) sourcePairEq)
  simp only [PiSCat.comp_obj] at h ⊢
  dsimp only [elvWeightUnitApp, elvBlockAdj, BalancedInduction.adjunction, elvBlockEval, Pi.eval,
    Functor.comp_obj, Functor.id_obj, Superfunctor.obj, Superfunctor.comp, elvBlockRes] at h ⊢
  exact h

local notation "hUpper" => elvMixedUpper_content_eq D i j Λ h₁ h₂ h₃ h₄ β
local notation "hComm" => blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β
local notation "L" => contentAppendTo D Sc cutoff bound (Subtype.val (blockSucc D Λ j h₁ β)) [i]
  (Subtype.val (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β))) hUpper
local notation "targetPairEq" => elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound i j Λ h₁ h₂ β
  (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)) hComm

/-- The selected lower weight cap commutes with the supported pair and target coordinates. -/
theorem elvWeightMixedCounit_comparison (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    (elvInductionComponent D Sc cutoff bound i Λ h₂ ε).map
      ((elvWeightCounit D Sc cutoff bound j Λ h₁).app M) ≫
      eqToHom (elvInductionComponent_obj_of D Sc cutoff bound i Λ h₂ δj ε hComm M) =
    eqToHom (congrArg (fun F => CategoryTheory.Functor.obj F ((Fj).obj M)) targetPairEq) ≫
      (BalancedInduction.induction L).map ((BalancedInduction.adjunctionCounit J).app (M δj)) := by
  have hm := elvInductionComponent_map_of D Sc cutoff bound i Λ h₂ δj ε hComm
    ((elvWeightCounit D Sc cutoff bound j Λ h₁).app M)
  dsimp only [elvWeightCounit] at hm
  rw [elvWeightCounitComponent_blockSucc] at hm
  have ht := congrArg
    (fun f => f ≫ eqToHom (elvInductionComponent_obj_of D Sc cutoff bound i Λ h₂ δj ε hComm M)) hm
  have h := map_counit_transport (BalancedInduction.induction L)
    (elvInductionComponent_obj_blockSucc D Sc cutoff bound j Λ h₁ β ((Fj).obj M))
    (elvInductionComponent_obj_of D Sc cutoff bound i Λ h₂ δj ε hComm
      ((elvE D Sc cutoff bound j Λ h₁).obj ((Fj).obj M)))
    (elvInductionComponent_obj_of D Sc cutoff bound i Λ h₂ δj ε hComm M)
    (congrArg (fun F => CategoryTheory.Functor.obj F ((Fj).obj M)) targetPairEq)
    ((BalancedInduction.adjunctionCounit J).app (M δj))
  dsimp only [elvBlockEval, Pi.eval, Functor.comp_obj, Functor.id_obj, Superfunctor.obj,
    Superfunctor.comp, elvBlockRes, elvBlockAdj, BalancedInduction.adjunction, elvWeightCounit] at h ht ⊢
  exact ht.trans h

end OddMath.QuiverHecke.ELVOld
