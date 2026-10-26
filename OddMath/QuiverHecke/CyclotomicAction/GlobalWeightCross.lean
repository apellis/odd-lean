/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightBlockCross
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightDot

/-!
# The crossing on weight spaces

Ports `globalCross` of `Categorification/KLR/CyclotomicAction/GlobalCross.lean`
to the weight spaces. Two global content inductions are the block induction
`heightBlockInduction₂` followed by an identity transport of heights
(`globalContentInduction_comp`). At a block `ε = s_i (s_j β)` of weight `d` the
crossing is `heightBlockCross`, transported along these identifications; at a
block that is not of this form both composites vanish. The result is the
`cross` field of `RouquierData` on weight spaces, of parity `|i||j|`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

section Content
variable (i j : I)

theorem globalContentInduction_comp_aux (β : Multiset I) {n m l : ℕ} (e₁ : n + 1 = m)
    (e₂ : m + 1 = l) (e₃ : n + 1 + 1 = l) :
    ((heightContentInduction D Sc j a ha n β).comp
        (heightContentCast D Sc a ha e₁ (rfl : {j} + β = {j} + β))).comp
      ((heightContentInduction D Sc i a ha m ({j} + β)).comp
        (heightContentCast D Sc a ha e₂ (rfl : {i} + ({j} + β) = {i} + ({j} + β)))) =
    (heightBlockInduction₂ D Sc a ha i j n β _ rfl).comp
      (heightContentCast D Sc a ha e₃ (rfl : {i} + ({j} + β) = {i} + ({j} + β))) := by
  subst e₁
  subst e₂
  rfl

omit [Fintype I] in
theorem card_of_add₂ {β ε : Multiset I} (h : {i} + ({j} + β) = ε) : β.card + 1 + 1 = ε.card := by
  subst h
  simp only [Multiset.card_add, Multiset.card_singleton]
  omega

/-- Two global content inductions are the two-step block induction followed by an identity
transport of heights. -/
theorem globalContentInduction_comp {β β' ε : Multiset I} (h₁ : {j} + β = β')
    (h₂ : {i} + β' = ε) :
    (globalContentInduction D Sc j a ha h₁).comp (globalContentInduction D Sc i a ha h₂) =
      (heightBlockInduction₂ D Sc a ha i j β.card β ε (by rw [h₁, h₂])).comp
        (heightContentCast D Sc a ha (card_of_add₂ i j (by rw [h₁, h₂])) rfl) := by
  subst h₁
  subst h₂
  exact globalContentInduction_comp_aux D Sc a ha i j β _ _ _

end Content

section Weight
variable (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X} (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

/-- The block reached by inducing `j` then `i`. -/
abbrev blockSucc₂ (β : WeightBlocks D Λ x₀) : WeightBlocks D Λ x₃ :=
  blockSucc D Λ i h₂ (blockSucc D Λ j h₁ β)

omit [Fintype I] in
theorem blockSucc₂_injective : Function.Injective (blockSucc₂ D i j Λ h₁ h₂) := fun _ _ e =>
  blockSucc_injective D Λ j h₁ (blockSucc_injective D Λ i h₂ e)

omit [Fintype I] in
theorem blockSucc₂_swap {β : WeightBlocks D Λ x₀} {ε : WeightBlocks D Λ x₃}
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) : blockSucc₂ D j i Λ h₃ h₄ β = ε :=
  Subtype.ext ((add_left_comm _ _ _).trans (congrArg Subtype.val hε))

/-- Composite induction at a two-step successor block is two-step block induction. -/
theorem globalEFunctor_comp_eq {β : WeightBlocks D Λ x₀} {ε : WeightBlocks D Λ x₃}
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    globalEFunctor D Sc a ha j Λ h₁ ⋙ (inductionComponent D Sc a ha i Λ h₂ ε).toFunctor =
      Pi.eval (fun β : WeightBlocks D Λ x₀ => GlobalContentModules D Sc a ha β.1) β ⋙
        ((heightBlockInduction₂ D Sc a ha i j β.1.card β.1 ε.1 (congrArg Subtype.val hε)).comp
          (heightContentCast D Sc a ha (card_of_add₂ i j (congrArg Subtype.val hε)) rfl)).toFunctor := by
  subst hε
  have e₁ := inductionComponent_blockSucc D Sc a ha i Λ h₂ (blockSucc D Λ j h₁ β)
  have e₂ := inductionComponent_blockSucc D Sc a ha j Λ h₁ β
  have e₃ := globalContentInduction_comp D Sc a ha i j (blockSucc_val D Λ j h₁ β).symm
    (blockSucc_val D Λ i h₂ (blockSucc D Λ j h₁ β)).symm
  calc globalEFunctor D Sc a ha j Λ h₁ ⋙
        (inductionComponent D Sc a ha i Λ h₂ (blockSucc₂ D i j Λ h₁ h₂ β)).toFunctor
      = globalEFunctor D Sc a ha j Λ h₁ ⋙
          ((blockEval D Sc a ha Λ (blockSucc D Λ j h₁ β)).comp
            (globalContentInduction D Sc i a ha
              (blockSucc_val D Λ i h₂ (blockSucc D Λ j h₁ β)).symm)).toFunctor := by
        rw [e₁]
    _ = (inductionComponent D Sc a ha j Λ h₁ (blockSucc D Λ j h₁ β)).toFunctor ⋙
          (globalContentInduction D Sc i a ha
            (blockSucc_val D Λ i h₂ (blockSucc D Λ j h₁ β)).symm).toFunctor := rfl
    _ = ((blockEval D Sc a ha Λ β).comp
            (globalContentInduction D Sc j a ha (blockSucc_val D Λ j h₁ β).symm)).toFunctor ⋙
          (globalContentInduction D Sc i a ha
            (blockSucc_val D Λ i h₂ (blockSucc D Λ j h₁ β)).symm).toFunctor := by
        rw [e₂]
    _ = Pi.eval (fun β : WeightBlocks D Λ x₀ => GlobalContentModules D Sc a ha β.1) β ⋙
          ((globalContentInduction D Sc j a ha (blockSucc_val D Λ j h₁ β).symm).comp
            (globalContentInduction D Sc i a ha
              (blockSucc_val D Λ i h₂ (blockSucc D Λ j h₁ β)).symm)).toFunctor := rfl
    _ = _ := by rw [e₃]

/-- The content crossing between the two block inductions, followed by the height transport. -/
def contentCross (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ x₃)
    (hc : {i} + ({j} + β.1) = ε.1) :
    (heightBlockInduction₂ D Sc a ha i j β.1.card β.1 ε.1 hc).comp
        (heightContentCast D Sc a ha (card_of_add₂ i j hc) rfl) ⟶
      (heightBlockInduction₂ D Sc a ha j i β.1.card β.1 ε.1 (swapped_content i j _ _ hc)).comp
        (heightContentCast D Sc a ha (card_of_add₂ i j hc) rfl) :=
  Superfunctor.whiskerRight (heightBlockCross D Sc a ha i j β.1.card β.1 ε.1 hc) _

theorem contentCross_app_eq_zero (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ x₃)
    (hc : {i} + ({j} + β.1) = ε.1) {q : ZMod 2} (hq : q ≠ D.parity i * D.parity j)
    (M : GlobalContentModules D Sc a ha β.1) :
    (contentCross D Sc a ha i j Λ β ε hc).app q M = 0 := by
  change (heightContentCast D Sc a ha (card_of_add₂ i j hc) rfl).map
    ((heightBlockCross D Sc a ha i j β.1.card β.1 ε.1 hc).app q M) = 0
  rw [congrFun (heightBlockCross_homogeneous D Sc a ha i j β.1.card β.1 ε.1 hc q hq) M]
  exact Functor.map_zero _ _ _

/-- The crossing component at a two-step successor block with a chosen source block. -/
def globalWeightCrossVia (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x₀) (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    (globalEFunctor D Sc a ha j Λ h₁ ⋙ (inductionComponent D Sc a ha i Λ h₂ ε).toFunctor).obj M ⟶
      (globalEFunctor D Sc a ha i Λ h₃ ⋙ (inductionComponent D Sc a ha j Λ h₄ ε).toFunctor).obj M :=
  eqToHom (Functor.congr_obj (globalEFunctor_comp_eq D Sc a ha i j Λ h₁ h₂ hε) M) ≫
    (contentCross D Sc a ha i j Λ β ε (congrArg Subtype.val hε)).app p (M β) ≫
      eqToHom (Functor.congr_obj (globalEFunctor_comp_eq D Sc a ha j i Λ h₃ h₄
        (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε)) M).symm

theorem globalWeightCrossVia_eq (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x₀)
    (β β' : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ x₃)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) (hε' : blockSucc₂ D i j Λ h₁ h₂ β' = ε) :
    globalWeightCrossVia D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M β ε hε =
      globalWeightCrossVia D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M β' ε hε' := by
  obtain rfl := blockSucc₂_injective D i j Λ h₁ h₂ (hε.trans hε'.symm)
  rfl

open scoped Classical in
/-- The crossing component at a block of weight `x₃`. -/
def globalWeightCrossComponent (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x₀)
    (ε : WeightBlocks D Λ x₃) :
    (globalEFunctor D Sc a ha j Λ h₁ ⋙ (inductionComponent D Sc a ha i Λ h₂ ε).toFunctor).obj M ⟶
      (globalEFunctor D Sc a ha i Λ h₃ ⋙ (inductionComponent D Sc a ha j Λ h₄ ε).toFunctor).obj M :=
  if hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε then
    globalWeightCrossVia D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M hε.choose ε hε.choose_spec
  else 0

theorem globalWeightCrossComponent_of (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x₀)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ x₃)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    globalWeightCrossComponent D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M ε =
      globalWeightCrossVia D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M β ε hε := by
  unfold globalWeightCrossComponent
  split
  · rename_i hc
    exact globalWeightCrossVia_eq D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M _ β ε hc.choose_spec hε
  · rename_i hc
    exact absurd ⟨β, hε⟩ hc

/-- Away from two-step successor blocks the composite induction vanishes. -/
theorem globalEFunctor_comp_isZero (ε : WeightBlocks D Λ x₃)
    (hε : ¬ ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε) (M : WeightProduct D Sc a ha Λ x₀) :
    Limits.IsZero
      ((globalEFunctor D Sc a ha j Λ h₁ ⋙ (inductionComponent D Sc a ha i Λ h₂ ε).toFunctor).obj M) := by
  by_cases hγ : ∃ γ, blockSucc D Λ i h₂ γ = ε
  · obtain ⟨γ, rfl⟩ := hγ
    have hz : Limits.IsZero ((globalEFunctor D Sc a ha j Λ h₁).obj M γ) :=
      inductionComponent_isZero D Sc a ha j Λ h₁ γ
        (fun ⟨β, hβ⟩ => hε ⟨β, by rw [blockSucc₂, hβ]⟩) M
    refine Limits.IsZero.of_iso ((blockInd D Sc a ha i Λ h₂ γ).toFunctor.map_isZero hz)
      (eqToIso (inductionComponent_obj_blockSucc D Sc a ha i Λ h₂ γ _))
  · exact inductionComponent_isZero D Sc a ha i Λ h₂ ε hγ _

theorem globalWeightCrossComponent_mem (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x₀)
    (ε : WeightBlocks D Λ x₃) :
    globalWeightCrossComponent D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M ε ∈ parity (R := k) _ _ p := by
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [globalWeightCrossComponent_of D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M β ε hβ]
    unfold globalWeightCrossVia
    have hm := comp_mem (eqToHom_mem_parity_zero
        (Functor.congr_obj (globalEFunctor_comp_eq D Sc a ha i j Λ h₁ h₂ hβ) M))
      (comp_mem ((contentCross D Sc a ha i j Λ β ε (congrArg Subtype.val hβ)).app_mem p (M β))
        (eqToHom_mem_parity_zero (Functor.congr_obj (globalEFunctor_comp_eq D Sc a ha j i Λ h₃ h₄
          (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hβ)) M).symm))
    simpa only [zero_add, add_zero] using hm
  · rw [(globalEFunctor_comp_isZero D Sc a ha i j Λ h₁ h₂ ε hε M).eq_of_src
      (globalWeightCrossComponent D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M ε) 0]
    exact Submodule.zero_mem _

theorem globalWeightCrossComponent_naturality (p : ZMod 2) (ε : WeightBlocks D Λ x₃)
    {M M' : WeightProduct D Sc a ha Λ x₀} {q : ZMod 2} (f : M ⟶ M')
    (hf : f ∈ parity (R := k) M M' q) :
    (globalEFunctor D Sc a ha j Λ h₁ ⋙ (inductionComponent D Sc a ha i Λ h₂ ε).toFunctor).map f ≫
        globalWeightCrossComponent D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M' ε =
      koszulSign p q • (globalWeightCrossComponent D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M ε ≫
        (globalEFunctor D Sc a ha i Λ h₃ ⋙
          (inductionComponent D Sc a ha j Λ h₄ ε).toFunctor).map f) := by
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [globalWeightCrossComponent_of D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M β ε hβ,
      globalWeightCrossComponent_of D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M' β ε hβ]
    unfold globalWeightCrossVia
    rw [Functor.congr_hom (globalEFunctor_comp_eq D Sc a ha i j Λ h₁ h₂ hβ) f,
      Functor.congr_hom (globalEFunctor_comp_eq D Sc a ha j i Λ h₃ h₄
        (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hβ)) f]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    have hn := (contentCross D Sc a ha i j Λ β ε (congrArg Subtype.val hβ)).naturality p (f β)
      (hf β)
    have hn' : ∀ {Z : GlobalContentModules D Sc a ha ε.1}
        (z : ((heightBlockInduction₂ D Sc a ha j i β.1.card β.1 ε.1
          (swapped_content i j _ _ (congrArg Subtype.val hβ))).comp
            (heightContentCast D Sc a ha (card_of_add₂ i j (congrArg Subtype.val hβ)) rfl)).obj
              (M' β) ⟶ Z),
        (Pi.eval (fun β : WeightBlocks D Λ x₀ => GlobalContentModules D Sc a ha β.1) β ⋙
          ((heightBlockInduction₂ D Sc a ha i j β.1.card β.1 ε.1 (congrArg Subtype.val hβ)).comp
            (heightContentCast D Sc a ha (card_of_add₂ i j (congrArg Subtype.val hβ))
              rfl)).toFunctor).map f ≫
          (contentCross D Sc a ha i j Λ β ε (congrArg Subtype.val hβ)).app p (M' β) ≫ z =
        koszulSign p q • ((contentCross D Sc a ha i j Λ β ε (congrArg Subtype.val hβ)).app p (M β) ≫
          (Pi.eval (fun β : WeightBlocks D Λ x₀ => GlobalContentModules D Sc a ha β.1) β ⋙
            ((heightBlockInduction₂ D Sc a ha j i β.1.card β.1 ε.1
              (swapped_content i j _ _ (congrArg Subtype.val hβ))).comp
              (heightContentCast D Sc a ha (card_of_add₂ i j (congrArg Subtype.val hβ))
                rfl)).toFunctor).map f ≫ z) := by
      intro Z z
      rw [← Category.assoc]
      erw [hn]
      rw [Linear.smul_comp, Category.assoc]
      rfl
    rw [hn', Linear.comp_smul]
  · exact (globalEFunctor_comp_isZero D Sc a ha i j Λ h₁ h₂ ε hε M).eq_of_src _ _

/-- **The crossing on weight spaces**, between the two composites of induction. -/
def globalWeightCross :
    SuperNatTrans k (globalEFunctor D Sc a ha j Λ h₁ ⋙ globalEFunctor D Sc a ha i Λ h₂)
      (globalEFunctor D Sc a ha i Λ h₃ ⋙ globalEFunctor D Sc a ha j Λ h₄) where
  app p M ε := globalWeightCrossComponent D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M ε
  app_mem p M ε := globalWeightCrossComponent_mem D Sc a ha i j Λ h₁ h₂ h₃ h₄ p M ε
  naturality p M M' q f hf := by
    funext ε
    exact globalWeightCrossComponent_naturality D Sc a ha i j Λ h₁ h₂ h₃ h₄ p ε f hf

/-- Only the component of parity `|i||j|` is nonzero. -/
theorem globalWeightCross_homogeneous :
    (globalWeightCross D Sc a ha i j Λ h₁ h₂ h₃ h₄).IsHomogeneous (D.parity i * D.parity j) := by
  intro q hq
  funext M
  funext ε
  change globalWeightCrossComponent D Sc a ha i j Λ h₁ h₂ h₃ h₄ q M ε = 0
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [globalWeightCrossComponent_of D Sc a ha i j Λ h₁ h₂ h₃ h₄ q M β ε hβ]
    unfold globalWeightCrossVia
    rw [contentCross_app_eq_zero D Sc a ha i j Λ β ε _ hq]
    simp
  · exact (globalEFunctor_comp_isZero D Sc a ha i j Λ h₁ h₂ ε hε M).eq_of_src _ _

/-- The crossing as a 2-morphism of the action target. -/
def globalActionCross :
    globalActionE D Sc a ha j Λ h₁ ≫ globalActionE D Sc a ha i Λ h₂ ⟶
      globalActionE D Sc a ha i Λ h₃ ≫ globalActionE D Sc a ha j Λ h₄ :=
  globalWeightCross D Sc a ha i j Λ h₁ h₂ h₃ h₄

/-- The crossing has parity `|i||j|`. -/
theorem globalActionCross_mem :
    globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄ ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  Superfunctor.mem_parity_iff_isHomogeneous.2
    (globalWeightCross_homogeneous D Sc a ha i j Λ h₁ h₂ h₃ h₄)

end Weight

end OddMath.QuiverHecke.CyclotomicAction
