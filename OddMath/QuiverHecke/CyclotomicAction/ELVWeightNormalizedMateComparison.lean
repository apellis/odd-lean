/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedMateInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightNormalizedRectangularCross
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightLocalMate

/-! # Normalized weight mate in content coordinates

Brundan–Ellis (1.12)–(1.14): the selected cup-crossing-cap retains the
negative equal-colour crossing and positive distinct-colour crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem mate_transport
    {A B : Type*} [Category* A] [Category* B] (R : A ⥤ B)
    {P Q : B} {S T V S' T' V' : A}
    (hP : P = Q) (hS : S = S') (hT : T = T') (hV : V = V')
    (η : P ⟶ R.obj S) (χ : S ⟶ T) (ε : T ⟶ V)
    (η' : Q ⟶ R.obj S') (χ' : S' ⟶ T') (ε' : T' ⟶ V')
    (hu : η ≫ R.map (eqToHom hS) = eqToHom hP ≫ η')
    (hx : χ = (eqToHom hS ≫ χ') ≫ eqToHom hT.symm)
    (hc : ε ≫ eqToHom hV = eqToHom hT ≫ ε') :
    ((η ≫ R.map χ) ≫ R.map ε) ≫ R.map (eqToHom hV) =
      eqToHom hP ≫ ((η' ≫ R.map χ') ≫ R.map ε') := by
  subst Q
  subst S'
  subst T'
  subst V'
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp] at hu hx hc ⊢
  rw [hu, hx, hc]

private theorem rectangularMate_expansion
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Category.{u} A] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (U : B ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
    {p : ZMod 2} {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ U).obj s}
    (hα : IsSupernatural k p α) (N : Superfunctor k A (SVec k)) :
    BalancedInduction.orderedRectangularMateComponent J K L U hα N =
      ((BalancedInduction.adjunctionUnit U).app
          (BalancedInduction.induced K ((BalancedInduction.restriction J).obj N)) ≫
        (BalancedInduction.restriction U).map (BalancedInduction.rectangularCrossComponent J K L U hα
          ((BalancedInduction.restriction J).obj N))) ≫
        (BalancedInduction.restriction U).map
          ((BalancedInduction.induction L).map ((BalancedInduction.adjunctionCounit J).app N)) := by
  exact (Category.assoc _ _ _).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Fj" => elvF D Sc cutoff bound j Λ h₁
local notation "Ei" => elvE D Sc cutoff bound i Λ h₃
local notation "Cross" => elvActionCross D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂

variable (β : WeightBlocks D Λ x₀)
local notation "δj" => blockSucc D Λ j h₁ β
local notation "δi" => blockSucc D Λ i h₃ β
local notation "ε" => blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)
local notation "hComm" => blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β
local notation "J" => elvBlockAppend D Sc cutoff bound j Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff bound i Λ h₃ β
local notation "U" => elvBlockAppend D Sc cutoff bound j Λ h₄ (blockSucc D Λ i h₃ β)
local notation "L" => contentAppendTo D Sc cutoff bound (Subtype.val (blockSucc D Λ j h₁ β)) [i]
  (Subtype.val (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)))
  (elvMixedUpper_content_eq D i j Λ h₁ h₂ h₃ h₄ β)
local notation "hα" => normalizedContentTargetsCross_supernatural D Sc cutoff bound (Subtype.val β) i j
  (Subtype.val (blockSucc D Λ j h₁ β)) (Subtype.val (blockSucc D Λ i h₃ β))
  (Subtype.val (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)))
  (elvBlockSucc_content_eq D j Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₃ β)
  (elvMixedUpper_content_eq D i j Λ h₁ h₂ h₃ h₄ β)
  (elvBlockSucc_content_eq D j Λ h₄ (blockSucc D Λ i h₃ β))
local notation "sourcePairEq" => elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound j i Λ h₃ h₄ β
  (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)) rfl
local notation "targetPairEq" => elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound i j Λ h₁ h₂ β
  (blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)) hComm

/-- The whole prescribed weight mate agrees with the normalized content mate on every supported block. -/
theorem elvWeightNormalizedMate_comparison
    (M : ELVWeightProduct D Sc cutoff bound Λ xj) :
    (elvWeightMixedMate D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄).app
        (D.parity i * D.parity j) M δi ≫
      eqToHom (elvWeightMixedTarget_obj D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β M) =
    eqToHom (elvWeightMixedSource_obj D Sc cutoff bound i j Λ h₁ h₃ β M) ≫
      BalancedInduction.orderedRectangularMateComponent J K L U hα (M δj) := by
  have hx := elvWeightCrossVia_normalized_rectangular D Sc cutoff bound j i Λ h₃ h₄ β ε rfl
    h₁ h₂ ((Fj).obj M)
  rw [mul_comm (D.parity j) (D.parity i)] at hx
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app] at hx
  have hw := elvWeightCross_supported D Sc cutoff bound j i Λ h₃ h₄ h₁ h₂
    (D.parity i * D.parity j) ((Fj).obj M) β ε rfl
  have hCross := hw.trans hx
  have hu := elvWeightMixedUnit_comparison D Sc cutoff bound i j Λ h₁ h₃ h₄ β M
  have hc := elvWeightMixedCounit_comparison D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β M
  have hp := mate_transport (BalancedInduction.restriction U)
    (elvWeightMixedSource_obj D Sc cutoff bound i j Λ h₁ h₃ β M)
    (congrArg (fun F => CategoryTheory.Functor.obj F ((Fj).obj M)) sourcePairEq)
    (congrArg (fun F => CategoryTheory.Functor.obj F ((Fj).obj M)) targetPairEq)
    (elvInductionComponent_obj_of D Sc cutoff bound i Λ h₂ δj ε hComm M)
    (elvWeightUnitApp D Sc cutoff bound j Λ h₄ δi ((Ei).obj ((Fj).obj M)))
    ((Cross).app (D.parity i * D.parity j) ((Fj).obj M) ε)
    ((elvInductionComponent D Sc cutoff bound i Λ h₂ ε).map
      ((elvWeightCounit D Sc cutoff bound j Λ h₁).app M))
    ((BalancedInduction.adjunctionUnit U).app
      (BalancedInduction.induced K ((BalancedInduction.restriction J).obj (M δj))))
    (BalancedInduction.rectangularCrossComponent J K L U hα ((BalancedInduction.restriction J).obj (M δj)))
    ((BalancedInduction.induction L).map ((BalancedInduction.adjunctionCounit J).app (M δj)))
    hu hCross hc
  rw [eqToHom_map, ← rectangularMate_expansion] at hp
  have ha := congrArg
    (fun f => f ≫ eqToHom (elvWeightMixedTarget_obj D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β M))
    (elvWeightMixedMate_app_block D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ (D.parity i * D.parity j) M δi)
  exact ha.trans hp

section RankOne
variable (a : I) {y₀ y₁ y₂ : X}
  (ha : y₀ + D.α a = y₁) (hb : y₁ + D.α a = y₂)
  (b : WeightBlocks D Λ y₀)
local notation "d" => blockSucc D Λ a ha b
local notation "e" => blockSucc D Λ a hb (blockSucc D Λ a ha b)
local notation "Lower" => elvBlockAppend D Sc cutoff bound a Λ ha b
local notation "Upper" => elvBlockAppend D Sc cutoff bound a Λ hb (blockSucc D Λ a ha b)
local notation "hχ" => normalizedContentTargetsCross_supernatural D Sc cutoff bound
  (Subtype.val b) a a (Subtype.val (blockSucc D Λ a ha b))
  (Subtype.val (blockSucc D Λ a ha b))
  (Subtype.val (blockSucc D Λ a hb (blockSucc D Λ a ha b)))
  (elvBlockSucc_content_eq D a Λ ha b) (elvBlockSucc_content_eq D a Λ ha b)
  (elvBlockSucc_content_eq D a Λ hb (blockSucc D Λ a ha b))
  (elvBlockSucc_content_eq D a Λ hb (blockSucc D Λ a ha b))
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff bound a Λ ha)
  (elvActionAdjunction D Sc cutoff bound a Λ hb)
  (elvActionCross D Sc cutoff bound a a Λ ha hb ha hb)

/-- The prescribed rank-one principal field retains the negative rectangular
crossing through its selected source and target content coordinates. -/
theorem elvWeightRouquierMate_comparison
    (N : ELVWeightProduct D Sc cutoff bound Λ y₁) :
    (φ).app (D.parity a) N d ≫
      eqToHom (elvWeightMixedTarget_obj D Sc cutoff bound a a Λ ha hb ha hb b N) =
    eqToHom (elvWeightMixedSource_obj D Sc cutoff bound a a Λ ha ha b N) ≫
      BalancedInduction.orderedRectangularMateComponent Lower Lower Upper Upper hχ (N d) := by
  rw [elvWeightRouquierMate_eq]
  have h := elvWeightNormalizedMate_comparison D Sc cutoff bound a a Λ ha hb ha hb b N
  have hp := congrArg
    (fun p => (elvWeightMixedMate D Sc cutoff bound a a Λ ha hb ha hb).app p N d)
    (SKM.zmod2_mul_self (D.parity a))
  exact (congrArg (fun f => f ≫ eqToHom
    (elvWeightMixedTarget_obj D Sc cutoff bound a a Λ ha hb ha hb b N)) hp.symm).trans h
end RankOne

end OddMath.QuiverHecke.ELVOld
