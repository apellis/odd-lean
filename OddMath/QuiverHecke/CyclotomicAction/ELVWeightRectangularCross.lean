/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMixedCoordinates

/-! # Weight pair comparison in rectangular content coordinates

The supported crossing comparison required by Brundan–Ellis (1.12)
retains the actual first successor and the prescribed upper block.
The chosen word comparison factors through the two literal append
inductions at these contents.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem transform_app_regrade
    {k C E : Type u} [CommRing k] [Category.{u} C] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (F G : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p q : ZMod 2} {α : ∀ s, F.obj s ⟶ G.obj s} (hpq : p = q)
    (hαp : IsSupernatural k p α) (hαq : IsSupernatural k q α)
    (P : Superfunctor k C (SVec k)) :
    (BalancedInduction.transform hαp).app p P = (BalancedInduction.transform hαq).app q P := by
  subst q
  rfl

private theorem comparison_cross_paste
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (Q : C ⥤ B) {S T : C ⥤ E} {S' T' U' V' : B ⥤ E}
    (eS : S ≅ Q ⋙ S') (eT : T ≅ Q ⋙ T') (fS : S' ≅ U') (fT : T' ≅ V')
    (χ : ∀ b, U'.obj b ⟶ V'.obj b) (M : C) :
    (((eS ≪≫ Functor.isoWhiskerLeft Q fS).hom.app M ≫ χ (Q.obj M)) ≫
      (eT ≪≫ Functor.isoWhiskerLeft Q fT).inv.app M) =
      (eS.hom.app M ≫ ((fS.hom.app (Q.obj M) ≫ χ (Q.obj M)) ≫ fT.inv.app (Q.obj M))) ≫
        eT.inv.app M := by
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.assoc]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

private theorem rectangular_eqIso_whiskerLeft
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    (Q : C ⥤ B) {F G : B ⥤ E} (h : F = G) :
    Functor.isoWhiskerLeft Q (eqToIso h) = eqToIso (congrArg (fun F => Q ⋙ F) h) := by
  cases h
  rfl

private theorem contentPairComparisonTo_eq
    (β : Multiset I) (i j : I) (δ γ : Multiset I)
    (hδ : β + ([i] : Multiset I) = δ) (hγ : δ + ([j] : Multiset I) = γ)
    (h : β + ([i,j] : Multiset I) = γ) :
    contentInductionCompTo D Sc cutoff bound β [i] δ hδ [j] γ hγ h =
      eqToIso (contentPairInductionTo_eq D Sc cutoff bound β i j δ γ hδ hγ h) ≪≫
        contentEPairToComparison D Sc cutoff bound β i j γ h := by
  apply Iso.ext
  exact contentPairComparisonTo_hom D Sc cutoff bound β i j δ γ hδ hγ h

private theorem contentWordCross_app_reverse
    (β γ : Multiset I) (i j : I)
    (hσ : β + ([i,j] : Multiset I) = γ) (hτ : β + ([j,i] : Multiset I) = γ)
    (P : ContentModules D Sc cutoff bound β) :
    (contentInductionTransform D Sc cutoff bound hσ hτ (contentCrossAffine_mem D Sc i j)).app
      (D.parity i * D.parity j) P =
    (contentInductionTransform D Sc cutoff bound (σ := [i] ++ [j]) (τ := [j] ++ [i])
      hσ hτ (contentCrossAffine_reverse_mem D Sc j i)).app (D.parity j * D.parity i) P := by
  exact transform_app_regrade _ _ (mul_comm (D.parity i) (D.parity j)) _ _ P

variable (i j : I) (Λ : X) {x₀ xj xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
  (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)

include h₂ hε in
/-- The final-content certificate keeps the first successor. -/
theorem elvWeightPairUpper_content_eq :
    (blockSucc D Λ j h₁ β).1 + ([i] : Multiset I) = ε.1 :=
  (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ j h₁ β)).trans
    (congrArg Subtype.val hε)

local notation "hj" => elvBlockSucc_content_eq D j Λ h₁ β
local notation "hUpper" => elvWeightPairUpper_content_eq D i j Λ h₁ h₂ β ε hε
local notation "hWord" => elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε
local notation "Pair" => contentInductionTo D Sc cutoff bound (Subtype.val β) [j]
  (Subtype.val (blockSucc D Λ j h₁ β)) hj ⋙
    contentInductionTo D Sc cutoff bound (Subtype.val (blockSucc D Λ j h₁ β)) [i]
      (Subtype.val ε) hUpper
local notation "Eval" => Superfunctor.toFunctor (elvBlockEval D Sc cutoff bound Λ β)

/-- The supported product coordinate is the literal two-append induction through its first block. -/
theorem elvEFunctor_comp₂_rectangular_eq :
    elvEFunctor D Sc cutoff bound j Λ h₁ ⋙
      (elvInductionComponent D Sc cutoff bound i Λ h₂ ε).toFunctor = Eval ⋙ Pair := by
  exact (elvEFunctor_comp₂_contentPair_eq D Sc cutoff bound i j Λ h₁ h₂ β ε hε).trans
    (congrArg (fun F => Eval ⋙ F)
      (contentPairInductionTo_eq D Sc cutoff bound β.1 j i
        (blockSucc D Λ j h₁ β).1 ε.1 hj hUpper hWord)).symm

/-- The independently selected weight comparison is exactly the rectangular-coordinate comparison. -/
theorem elvWeightPairComparison_rectangular_eq :
    elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε =
      eqToIso (elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound i j Λ h₁ h₂ β ε hε) ≪≫
        Functor.isoWhiskerLeft Eval
          (contentInductionCompTo D Sc cutoff bound β.1 [j]
            (blockSucc D Λ j h₁ β).1 hj [i] ε.1 hUpper hWord) := by
  rw [contentPairComparisonTo_eq, Functor.isoWhiskerLeft_trans,
    rectangular_eqIso_whiskerLeft, ← Iso.trans_assoc, eqToIso_trans]
  exact elvWeightPairComparison_eq D Sc cutoff bound i j Λ h₁ h₂ β ε hε

variable {xi : X} (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "hSwap" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε
local notation "hi" => elvBlockSucc_content_eq D i Λ h₃ β
local notation "hUpperSwap" => elvWeightPairUpper_content_eq D j i Λ h₃ h₄ β ε hSwap
local notation "J" => elvBlockAppend D Sc cutoff bound i Λ h₃ β
local notation "K" => elvBlockAppend D Sc cutoff bound j Λ h₁ β
local notation "L" => contentAppendTo D Sc cutoff bound
  (Subtype.val (blockSucc D Λ i h₃ β)) [j] (Subtype.val ε) hUpperSwap
local notation "U" => contentAppendTo D Sc cutoff bound
  (Subtype.val (blockSucc D Λ j h₁ β)) [i] (Subtype.val ε) hUpper
local notation "hα" => contentDistinctTargetsCross_supernatural D Sc cutoff bound
  (Subtype.val β) j i (Subtype.val (blockSucc D Λ i h₃ β))
  (Subtype.val (blockSucc D Λ j h₁ β)) (Subtype.val ε) hi hj hUpperSwap hUpper

/-- The selected supported weight crossing is the rectangular content crossing
in the independently chosen product-induction coordinates. -/
theorem elvWeightCrossVia_rectangular (hne : i ≠ j)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvWeightCrossVia D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε).app
      (D.parity i * D.parity j) M =
      ((eqToIso (elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound i j Λ h₁ h₂ β ε hε)).hom.app M ≫
        BalancedInduction.rectangularCrossComponent J K L U hα (M β)) ≫
        (eqToIso (elvEFunctor_comp₂_rectangular_eq D Sc cutoff bound j i Λ h₃ h₄ β ε hSwap)).inv.app M := by
  rw [elvWeightCrossVia_component, elvWeightPairComparison_rectangular_eq,
    elvWeightPairComparison_rectangular_eq]
  dsimp only [elvBlockEval, Pi.eval, Functor.comp_obj]
  rw [comparison_cross_paste]
  rw [contentWordCross_app_reverse]
  rw [contentDistinctTargetsCross_comparison D Sc cutoff bound β.1 j i
    (blockSucc D Λ i h₃ β).1 (blockSucc D Λ j h₁ β).1 ε.1 hi hj hUpperSwap hUpper
    (elvWeightPair_content_eq D j i Λ h₃ h₄ β ε hSwap) hWord hne.symm (M β)]

end OddMath.QuiverHecke.ELVOld
