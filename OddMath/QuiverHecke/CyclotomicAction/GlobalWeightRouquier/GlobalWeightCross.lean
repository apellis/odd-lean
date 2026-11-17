import StringDiagrams.Super.TwoSCat
import StringDiagrams.Super.PiTwo
import StringDiagrams.Super.SCat
import OddMath.QuiverHecke.CyclotomicAction.AppendContent.AppendDot
import OddMath.QuiverHecke.CyclotomicAction.CategoryGrading
import OddMath.QuiverHecke.CyclotomicAction.ContentModule.ContentParity
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeight.GlobalHeightBlockCross
import OddMath.QuiverHecke.CyclotomicAction.GlobalInduction.GlobalWeightInduction
import OddMath.SKM.RouquierMixedMate
import OddMath.SKM.RouquierMulticolour

/-!
# Global weight rouquier

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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

/-- The crossing as a 2-morphism of the action target. -/
def globalActionCross :
    globalActionE D Sc a ha j Λ h₁ ≫ globalActionE D Sc a ha i Λ h₂ ⟶
      globalActionE D Sc a ha i Λ h₃ ≫ globalActionE D Sc a ha j Λ h₄ :=
  globalWeightCross D Sc a ha i j Λ h₁ h₂ h₃ h₄

end Weight

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# Rouquier data on cyclotomic weight spaces

Ports `globalCross_sq` of `Categorification/KLR/CyclotomicAction/GlobalCross.lean` and the
data part of `GlobalFamily.lean`. The same-colour weight crossing squares to zero
(`globalWeightCross_square`, blockwise from `heightSuperInductionCrossing_square`). As in the
even file the Rouquier crossing is `-ψ` for equal colours and `ψ` otherwise
(`globalActionSignedCross`). Weight-space induction, the dot of parity `|i|` and the signed
crossing of parity `|i||j|` assemble to `globalRouquierData : SKM.RouquierData D` in the
supercategory of supercategories, and the adjunction and square fields hold
(`globalActionAdjunction`, `globalActionSignedCross_square`). The braid relation and the
local inversion field `loc` of `RouquierFamily` remain to be supplied.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (Λ : X)

section Square
variable (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

end Square

section Signed
variable [DecidableEq I] (i j : I) {x₀ x₁ x₂ x₃ : X} (h₁ : x₀ + D.α j = x₁)
  (h₂ : x₁ + D.α i = x₃) (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

/-- The Rouquier crossing on weight spaces: `-ψ` for equal colours, `ψ` otherwise. -/
def globalActionSignedCross :
    globalActionE D Sc a ha j Λ h₁ ≫ globalActionE D Sc a ha i Λ h₂ ⟶
      globalActionE D Sc a ha i Λ h₃ ≫ globalActionE D Sc a ha j Λ h₄ :=
  if i = j then -globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄
  else globalActionCross D Sc a ha i j Λ h₁ h₂ h₃ h₄

end Signed

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The equal-colour braid relation on weight spaces

Ports `globalCross_sameBraid` of `Categorification/KLR/CyclotomicAction/GlobalBraid.lean`
to the weight spaces. On content blocks the two crossings of three inductions are the
inner crossing `Ind(t)` and the outer crossing `t_{Ind}` of `GlobalHeightBraid`, conjugated
by identity transports of heights and contents (`heightContentBraid`). At a block that is
not a three-step successor the triple composite vanishes. Hence the weight crossing
satisfies `t₂ t₁ t₂ = t₁ t₂ t₁` with `t₁ = t ▷ E` and `t₂ = E ◁ t`
(`globalActionCross_braid`), and so does the signed Rouquier crossing `-t`
(`globalActionSignedCross_braid`): this is the `braid` field of `RouquierFamily`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

section Content
variable (i : I)

attribute [local irreducible] ContentSupported


end Content

section Weight
variable (i : I) (Λ : X) {x₀ x₁ x₂ x₃ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (h₃ : x₂ + D.α i = x₃)


end Weight

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The dot slides on weight spaces

Transports `heightInduction_slide_left/right` of `GlobalHeightSlides` through content blocks
and successor blocks to the weight spaces. With `t = -ψ` the Rouquier crossing,
`x₁` the dot of the inner and `x₂` the dot of the outer induction, and `s = (-1)^{|i|}`,

  `E₁ ◁ x₂ ≫ t - s (t ≫ x₁ ▷ E₂) = 1`,  `t ≫ E₁ ◁ x₂ - s (x₁ ▷ E₂ ≫ t) = 1`

(`globalActionSignedCross_slide_left/right`): the slide fields of `SuperRouquierLoc`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

omit [Fintype I] in
theorem zmod2_mul_self (p : ZMod 2) : p * p = p := by
  fin_cases p <;> rfl

section Content
variable (i : I)

attribute [local irreducible] ContentSupported

end Content

section Weight
variable [DecidableEq I] (i : I) (Λ : X) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁)
  (h₂ : x₁ + D.α i = x₂)

end Weight

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# Π-structures on the cyclotomic weight spaces

The weight spaces of the cyclotomic factor family are products of full subcategories of module
supercategories `A-SMod-k`, which are Π-supercategories (Brundan–Ellis, *Monoidal
supercategories*, arXiv:1603.05928v3, Example 1.8). Content support is cut out by an even
idempotent, so it is preserved by the parity shift `Π`
(`heightContentSupported_piObj`); full subcategories closed under `Π` and products of
Π-supercategories are Π-supercategories (`fullPiSupercategory`, `productPiSupercategory`).
Hence every weight space is a Π-supercategory (`globalWeightSpacePi`), and the factor family
`globalRouquierFamily` is a super Rouquier family in `Π-𝔖ℭ𝔞𝔱` (`globalPiRouquierFamily`), where
the morphism supercategories are Π-supercategories, as the swapped Hom construction requires.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v w t

section Full
variable {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
  [Preadditive C] [Linear k C] [Supercategory k C] (P : ObjectProperty C)

/-- `Π` on a full subcategory closed under `Π`, with the same `ζ`. -/
@[instance_reducible]
def fullPiSupercategory [PiSupercategory k C]
    (hP : ∀ M, P M → P ((PiSupercategory.pi (R := k)).obj M)) :
    PiSupercategory k P.FullSubcategory :=
  PiSupercategory.ofIso (fun M => ⟨(PiSupercategory.pi (R := k)).obj M.obj, hP _ M.property⟩)
    (fun M =>
      { hom := ⟨(PiSupercategory.ζ (R := k) M.obj).hom⟩
        inv := ⟨(PiSupercategory.ζ (R := k) M.obj).inv⟩
        hom_inv_id := InducedCategory.hom_ext (PiSupercategory.ζ (R := k) M.obj).hom_inv_id
        inv_hom_id := InducedCategory.hom_ext (PiSupercategory.ζ (R := k) M.obj).inv_hom_id })
    (fun M => PiSupercategory.ζ_hom_mem (R := k) M.obj)

end Full

section Product
variable {k : Type u} [CommRing k] {A : Type t}
  (C : A → Type v) [∀ a, Category.{w} (C a)] [∀ a, Preadditive (C a)]
  [∀ a, Linear k (C a)] [∀ a, Supercategory k (C a)]

/-- `Π` on a product of Π-supercategories, componentwise. -/
@[instance_reducible]
def productPiSupercategory [∀ a, PiSupercategory k (C a)] : PiSupercategory k (∀ a, C a) :=
  PiSupercategory.ofIso (fun M a => (PiSupercategory.pi (R := k)).obj (M a))
    (fun M =>
      { hom := fun a => (PiSupercategory.ζ (R := k) (M a)).hom
        inv := fun a => (PiSupercategory.ζ (R := k) (M a)).inv
        hom_inv_id := funext fun a => (PiSupercategory.ζ (R := k) (M a)).hom_inv_id
        inv_hom_id := funext fun a => (PiSupercategory.ζ (R := k) (M a)).inv_hom_id })
    (fun M a => PiSupercategory.ζ_hom_mem (R := k) (M a))

end Product

section Bimodule
variable {k : Type u} [CommRing k] {A : Type v} [Ring A] [Algebra k A] {B : Type w} [Ring B]
  [Algebra k B] {𝒜 : ZMod 2 → Submodule k A} {ℬ : ZMod 2 → Submodule k B} [GradedAlgebra 𝒜]

/-- An even element acts on `Π V` as on `V`. -/
theorem piObj_lact_apply_of_even (V : SuperBimodule 𝒜 ℬ) {e : A} (he : e ∈ 𝒜 0)
    (m : V.toSVec) : (SuperBimodule.piObj V).lact e m = V.lact e m := by
  rw [SuperBimodule.piObj_lact_of_mem V he]
  change (sign k 0 • V.lact e) m = _
  rw [sign_zero, one_smul]

end Bimodule

section Weight
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

/-- Content support is preserved by the parity shift: the content idempotent is even. -/
theorem heightContentSupported_piObj (n : ℕ) (β : Multiset I) (M : HeightModules D Sc a ha n)
    (hM : heightContentSupported D Sc a ha n β M) :
    heightContentSupported D Sc a ha n β ((PiSupercategory.pi (R := k)).obj M) := by
  cases n with
  | zero => exact hM
  | succ n =>
    intro m
    exact (piObj_lact_apply_of_even M (cyclotomicContentIdempotent_parity D Sc a ha n β) m).trans
      (hM m)

/-- Each content supercategory is a Π-supercategory. -/
@[instance_reducible]
def globalContentPi (β : Multiset I) : PiSupercategory k (GlobalContentModules D Sc a ha β) :=
  fullPiSupercategory _ fun M hM => heightContentSupported_piObj D Sc a ha β.card β M hM

variable (Λ x : X)

/-- Each weight space is a Π-supercategory, componentwise. -/
@[instance_reducible]
def globalWeightSpacePi : PiSupercategory k (globalWeightSpace D Sc a ha Λ x) :=
  letI := fun β : WeightBlocks D Λ x => globalContentPi D Sc a ha β.1
  productPiSupercategory _

end Weight

section Family
variable {I k : Type u} {X : Type u} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] [DecidableEq I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (Λ : X)

end Family

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-! # Full-ELV module categories at every original weight

Advances `DeformedActionAssembly.md` §5. All blocks of the original weight
group are retained. Induction uses the actual full-coefficient content append
functor at the unique predecessor block, and the zero module on absent
predecessors. Restriction uses the same append functor. Their adjunction is
assembled from the concrete balanced induction adjunction, including the
absent-colour boundary. No local inversion, polynomial replacement, faithful
model or finite-colour assumption is used.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- The zero vector superspace used for genuinely absent content predecessors. -/
abbrev elvZeroSpace : SVec.{u} k where
  carrier := PUnit.{u + 1}
  odd := 0
  odd_comp_odd := LinearMap.ext fun _ => rfl

/-- The underlying zero-module functor, before bundling its super structure. -/
abbrev elvZeroModuleFunctor (β : Multiset I) :
    ContentCategory D Sc cutoff bound β ⥤ SVec.{u} k where
  obj := fun _ => elvZeroSpace (k := k)
  map := fun _ => 0
  map_id := by intro v; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
  map_comp := by intros; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _

instance (β : Multiset I) : (elvZeroModuleFunctor D Sc cutoff bound β).Additive where
  map_add := by intros; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
instance (β : Multiset I) : (elvZeroModuleFunctor D Sc cutoff bound β).Linear k where
  map_smul := by intros; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
instance (β : Multiset I) : IsSuperfunctor k (elvZeroModuleFunctor D Sc cutoff bound β) where
  map_mem _ := Submodule.zero_mem _

/-- The zero module on the existing exact-content category. -/
abbrev elvZeroModule (β : Multiset I) : ContentModules D Sc cutoff bound β :=
  ⟨elvZeroModuleFunctor D Sc cutoff bound β⟩

theorem elvZeroModule_isZero (β : Multiset I) :
    Limits.IsZero (elvZeroModule D Sc cutoff bound β) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply Superfunctor.hom_ext
  intro p v
  apply SVec.hom_ext
  intro x
  exact Subsingleton.elim _ _

section ZeroFunctor
variable {C : Type*} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]

def elvZeroFunctor (β : Multiset I) : C ⥤ ContentModules D Sc cutoff bound β :=
  (Functor.const C).obj (elvZeroModule D Sc cutoff bound β)

instance (β : Multiset I) : (elvZeroFunctor D Sc cutoff bound (C := C) β).Additive where
  map_add := (elvZeroModule_isZero D Sc cutoff bound β).eq_of_src _ _
instance (β : Multiset I) : (elvZeroFunctor D Sc cutoff bound (C := C) β).Linear k where
  map_smul _ _ := (elvZeroModule_isZero D Sc cutoff bound β).eq_of_src _ _
instance (β : Multiset I) : IsSuperfunctor k (elvZeroFunctor D Sc cutoff bound (C := C) β) where
  map_mem {_ _ _ f} _ := by
    rw [(elvZeroModule_isZero D Sc cutoff bound β).eq_of_src
      ((elvZeroFunctor D Sc cutoff bound β).map f) 0]
    exact Submodule.zero_mem _
end ZeroFunctor

/-- All content blocks of one original weight; no quotient of the weight group. -/
abbrev ELVWeightProduct (Λ x : X) :=
  ∀ β : WeightBlocks D Λ x, ContentModules D Sc cutoff bound β.1

@[instance_reducible]
def elvWeightPi (Λ x : X) : PiSupercategory k (ELVWeightProduct D Sc cutoff bound Λ x) :=
  letI := fun β : WeightBlocks D Λ x => contentModulesPi D Sc cutoff bound β.1
  productPiSupercategory _

abbrev elvWeightSpace (Λ x : X) : PiSCat.{u, u, u + 1} k :=
  letI := elvWeightPi D Sc cutoff bound Λ x
  PiSCat.of k (ELVWeightProduct D Sc cutoff bound Λ x)

section Weight
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The actual append functor between a block and its exact successor. -/
abbrev elvBlockAppend (β : WeightBlocks D Λ x) :=
  contentAppendTo D Sc cutoff bound β.1 [i] (blockSucc D Λ i h β).1
    (by rw [blockSucc_val, add_comm]; rfl)

abbrev elvBlockInd (β : WeightBlocks D Λ x) :
    Superfunctor k (ContentModules D Sc cutoff bound β.1)
      (ContentModules D Sc cutoff bound (blockSucc D Λ i h β).1) :=
  ⟨BalancedInduction.induction (elvBlockAppend D Sc cutoff bound i Λ h β)⟩

abbrev elvBlockRes (β : WeightBlocks D Λ x) :
    Superfunctor k (ContentModules D Sc cutoff bound (blockSucc D Λ i h β).1)
      (ContentModules D Sc cutoff bound β.1) :=
  ⟨BalancedInduction.restriction (elvBlockAppend D Sc cutoff bound i Λ h β)⟩

abbrev elvBlockAdj (β : WeightBlocks D Λ x) :
    (elvBlockInd D Sc cutoff bound i Λ h β).toFunctor ⊣
      (elvBlockRes D Sc cutoff bound i Λ h β).toFunctor :=
  BalancedInduction.adjunction (elvBlockAppend D Sc cutoff bound i Λ h β)

def elvBlockEval (β : WeightBlocks D Λ x) :
    Superfunctor k (ELVWeightProduct D Sc cutoff bound Λ x)
      (ContentModules D Sc cutoff bound β.1) := ⟨Pi.eval _ β⟩

private def elvInductionVia (δ : WeightBlocks D Λ y) (β : WeightBlocks D Λ x)
    (hβ : blockSucc D Λ i h β = δ) :
    Superfunctor k (ELVWeightProduct D Sc cutoff bound Λ x)
      (ContentModules D Sc cutoff bound δ.1) := by
  subst δ
  exact (elvBlockEval D Sc cutoff bound Λ β).comp (elvBlockInd D Sc cutoff bound i Λ h β)

private theorem elvInductionVia_eq (δ : WeightBlocks D Λ y)
    (β β' : WeightBlocks D Λ x) (hβ : blockSucc D Λ i h β = δ)
    (hβ' : blockSucc D Λ i h β' = δ) :
    elvInductionVia D Sc cutoff bound i Λ h δ β hβ =
      elvInductionVia D Sc cutoff bound i Λ h δ β' hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  rfl

def elvInductionComponent (δ : WeightBlocks D Λ y) :
    Superfunctor k (ELVWeightProduct D Sc cutoff bound Λ x)
      (ContentModules D Sc cutoff bound δ.1) :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    elvInductionVia D Sc cutoff bound i Λ h δ hδ.choose hδ.choose_spec
  else ⟨elvZeroFunctor D Sc cutoff bound δ.1⟩

theorem elvInductionComponent_blockSucc (β : WeightBlocks D Λ x) :
    elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β) =
      (elvBlockEval D Sc cutoff bound Λ β).comp (elvBlockInd D Sc cutoff bound i Λ h β) := by
  unfold elvInductionComponent
  split
  · rename_i hc
    exact elvInductionVia_eq D Sc cutoff bound i Λ h _ _ β hc.choose_spec rfl
  · rename_i hn
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hn

theorem elvInductionComponent_isZero (δ : WeightBlocks D Λ y)
    (hδ : ¬ ∃ β, blockSucc D Λ i h β = δ)
    (M : ELVWeightProduct D Sc cutoff bound Λ x) :
    Limits.IsZero ((elvInductionComponent D Sc cutoff bound i Λ h δ).obj M) := by
  unfold elvInductionComponent
  split
  · exact absurd ‹_› hδ
  · exact elvZeroModule_isZero D Sc cutoff bound δ.1

def elvEFunctor : ELVWeightProduct D Sc cutoff bound Λ x ⥤
    ELVWeightProduct D Sc cutoff bound Λ y :=
  Functor.pi' fun δ => (elvInductionComponent D Sc cutoff bound i Λ h δ).toFunctor

instance : (elvEFunctor D Sc cutoff bound i Λ h).Additive where
  map_add := funext fun δ => (elvInductionComponent D Sc cutoff bound i Λ h δ).toFunctor.map_add
instance : (elvEFunctor D Sc cutoff bound i Λ h).Linear k where
  map_smul f r := funext fun δ =>
    (elvInductionComponent D Sc cutoff bound i Λ h δ).toFunctor.map_smul r f
instance : IsSuperfunctor k (elvEFunctor D Sc cutoff bound i Λ h) where
  map_mem hf δ := IsSuperfunctor.map_mem
    (F := (elvInductionComponent D Sc cutoff bound i Λ h δ).toFunctor) hf

def elvE : elvWeightSpace D Sc cutoff bound Λ x ⟶ elvWeightSpace D Sc cutoff bound Λ y :=
  ⟨elvEFunctor D Sc cutoff bound i Λ h⟩

def elvF : elvWeightSpace D Sc cutoff bound Λ y ⟶ elvWeightSpace D Sc cutoff bound Λ x :=
  ⟨productFunctor (fun δ : WeightBlocks D Λ y => ContentModules D Sc cutoff bound δ.1)
    (blockSucc D Λ i h) (fun β : WeightBlocks D Λ x => ContentModules D Sc cutoff bound β.1)
    (fun β => (elvBlockRes D Sc cutoff bound i Λ h β).toFunctor)⟩

theorem elvInductionComponent_obj_blockSucc (β : WeightBlocks D Λ x)
    (M : ELVWeightProduct D Sc cutoff bound Λ x) :
    (elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).obj M =
      (elvBlockInd D Sc cutoff bound i Λ h β).obj (M β) := by
  rw [elvInductionComponent_blockSucc]
  rfl

theorem elvInductionComponent_map_blockSucc (β : WeightBlocks D Λ x)
    {M M' : ELVWeightProduct D Sc cutoff bound Λ x} (f : M ⟶ M') :
    (elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).map f =
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M) ≫
        (elvBlockInd D Sc cutoff bound i Λ h β).map (f β) ≫
          eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M').symm :=
  superfunctor_map_of_eq (elvInductionComponent_blockSucc D Sc cutoff bound i Λ h β) f

/-- The unit component at a block of weight `x`. -/
def elvWeightUnitApp (β : WeightBlocks D Λ x) (M : ELVWeightProduct D Sc cutoff bound Λ x) :
    M β ⟶ (elvBlockRes D Sc cutoff bound i Λ h β).obj
      ((elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).obj M) :=
  (elvBlockAdj D Sc cutoff bound i Λ h β).unit.app (M β) ≫
    (elvBlockRes D Sc cutoff bound i Λ h β).map
      (eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M).symm)

theorem elvWeightUnitApp_naturality (β : WeightBlocks D Λ x)
    {M M' : ELVWeightProduct D Sc cutoff bound Λ x} (f : M ⟶ M') :
    f β ≫ elvWeightUnitApp D Sc cutoff bound i Λ h β M' =
      elvWeightUnitApp D Sc cutoff bound i Λ h β M ≫ (elvBlockRes D Sc cutoff bound i Λ h β).map
        ((elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [elvInductionComponent_map_blockSucc]
  simp only [elvWeightUnitApp, Superfunctor.map, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [Functor.map_comp, ← Adjunction.unit_naturality_assoc]

/-- The unit on weight spaces. -/
def elvWeightUnit : 𝟭 (ELVWeightProduct D Sc cutoff bound Λ x) ⟶
    elvEFunctor D Sc cutoff bound i Λ h ⋙ (elvF D Sc cutoff bound i Λ h).toFunctor where
  app M β := elvWeightUnitApp D Sc cutoff bound i Λ h β M
  naturality _ _ f := funext fun β => elvWeightUnitApp_naturality D Sc cutoff bound i Λ h β f

/-- The counit at a block with a chosen predecessor. -/
def elvWeightCounitVia (N : ELVWeightProduct D Sc cutoff bound Λ y) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (elvInductionComponent D Sc cutoff bound i Λ h δ).obj ((elvF D Sc cutoff bound i Λ h).obj N) ⟶ N δ := by
  subst hβ
  exact eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β _) ≫
    (elvBlockAdj D Sc cutoff bound i Λ h β).counit.app (N (blockSucc D Λ i h β))

theorem elvWeightCounitVia_eq (N : ELVWeightProduct D Sc cutoff bound Λ y) (β β' : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) (hβ' : blockSucc D Λ i h β' = δ) :
    elvWeightCounitVia D Sc cutoff bound i Λ h N β δ hβ =
      elvWeightCounitVia D Sc cutoff bound i Λ h N β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The counit component at a block: through the predecessor, or zero. -/
def elvWeightCounitComponent (N : ELVWeightProduct D Sc cutoff bound Λ y) (δ : WeightBlocks D Λ y) :
    (elvInductionComponent D Sc cutoff bound i Λ h δ).obj ((elvF D Sc cutoff bound i Λ h).obj N) ⟶ N δ :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    elvWeightCounitVia D Sc cutoff bound i Λ h N hδ.choose δ hδ.choose_spec
  else 0

theorem elvWeightCounitComponent_blockSucc (N : ELVWeightProduct D Sc cutoff bound Λ y)
    (β : WeightBlocks D Λ x) :
    elvWeightCounitComponent D Sc cutoff bound i Λ h N (blockSucc D Λ i h β) =
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β
        ((elvF D Sc cutoff bound i Λ h).obj N)) ≫
        (elvBlockAdj D Sc cutoff bound i Λ h β).counit.app (N (blockSucc D Λ i h β)) := by
  unfold elvWeightCounitComponent
  split
  · rename_i hc
    exact elvWeightCounitVia_eq D Sc cutoff bound i Λ h N _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem elvWeightCounitComponent_naturality (β : WeightBlocks D Λ x)
    {N N' : ELVWeightProduct D Sc cutoff bound Λ y} (g : N ⟶ N') :
    (elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).map
        ((elvF D Sc cutoff bound i Λ h).map g) ≫
      elvWeightCounitComponent D Sc cutoff bound i Λ h N' (blockSucc D Λ i h β) =
    elvWeightCounitComponent D Sc cutoff bound i Λ h N (blockSucc D Λ i h β) ≫
      g (blockSucc D Λ i h β) := by
  rw [elvInductionComponent_map_blockSucc, elvWeightCounitComponent_blockSucc,
    elvWeightCounitComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  congr 1
  exact (elvBlockAdj D Sc cutoff bound i Λ h β).counit_naturality (g (blockSucc D Λ i h β))

/-- The counit on weight spaces. -/
def elvWeightCounit : (elvF D Sc cutoff bound i Λ h).toFunctor ⋙ elvEFunctor D Sc cutoff bound i Λ h ⟶
    𝟭 (ELVWeightProduct D Sc cutoff bound Λ y) where
  app N δ := elvWeightCounitComponent D Sc cutoff bound i Λ h N δ
  naturality N N' g := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact elvWeightCounitComponent_naturality D Sc cutoff bound i Λ h β g
    · exact (elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ _).eq_of_src _ _

theorem elvWeight_left_triangle (β : WeightBlocks D Λ x) (M : ELVWeightProduct D Sc cutoff bound Λ x) :
    (elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).map
        ((elvWeightUnit D Sc cutoff bound i Λ h).app M) ≫
      elvWeightCounitComponent D Sc cutoff bound i Λ h ((elvEFunctor D Sc cutoff bound i Λ h).obj M)
        (blockSucc D Λ i h β) = 𝟙 _ := by
  rw [elvInductionComponent_map_blockSucc, elvWeightCounitComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  change eqToHom _ ≫ (elvBlockInd D Sc cutoff bound i Λ h β).map (elvWeightUnitApp D Sc cutoff bound i Λ h β M) ≫
    _ = _
  simp only [elvWeightUnitApp, Superfunctor.map, Functor.map_comp, Category.assoc]
  erw [Adjunction.counit_naturality, Adjunction.left_triangle_components_assoc]
  simp

theorem elvWeight_right_triangle (β : WeightBlocks D Λ x) (N : ELVWeightProduct D Sc cutoff bound Λ y) :
    elvWeightUnitApp D Sc cutoff bound i Λ h β ((elvF D Sc cutoff bound i Λ h).obj N) ≫
      (elvBlockRes D Sc cutoff bound i Λ h β).map
        (elvWeightCounitComponent D Sc cutoff bound i Λ h N (blockSucc D Λ i h β)) = 𝟙 _ := by
  rw [elvWeightCounitComponent_blockSucc]
  simp only [elvWeightUnitApp, Superfunctor.map, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact (elvBlockAdj D Sc cutoff bound i Λ h β).right_triangle_components _

/-- **Induction is left adjoint to restriction on weight spaces.** -/
def elvWeightAdjunction :
    elvEFunctor D Sc cutoff bound i Λ h ⊣ (elvF D Sc cutoff bound i Λ h).toFunctor where
  unit := elvWeightUnit D Sc cutoff bound i Λ h
  counit := elvWeightCounit D Sc cutoff bound i Λ h
  left_triangle_components M := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact elvWeight_left_triangle D Sc cutoff bound i Λ h β M
    · exact (elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ _).eq_of_src _ _
  right_triangle_components N := funext fun β => elvWeight_right_triangle D Sc cutoff bound i Λ h β N

theorem elvBlockAdj_unit_mem (β : WeightBlocks D Λ x)
    (M : ContentModules D Sc cutoff bound β.1) :
    (elvBlockAdj D Sc cutoff bound i Λ h β).unit.app M ∈ parity (R := k) _ _ 0 := by
  change (BalancedInduction.unitTransform (elvBlockAppend D Sc cutoff bound i Λ h β) M).app 1 = 0
  funext w
  simp only [BalancedInduction.unitTransform_app, one_ne_zero, ↓reduceIte, Pi.zero_apply]

theorem elvBlockAdj_counit_mem (β : WeightBlocks D Λ x)
    (M : ContentModules D Sc cutoff bound (blockSucc D Λ i h β).1) :
    (elvBlockAdj D Sc cutoff bound i Λ h β).counit.app M ∈ parity (R := k) _ _ 0 := by
  change (BalancedInduction.counitTransform (elvBlockAppend D Sc cutoff bound i Λ h β) M).app 1 = 0
  funext w
  simp only [BalancedInduction.counitTransform_app, one_ne_zero, ↓reduceIte, Pi.zero_apply]

theorem elvWeightUnitApp_mem (β : WeightBlocks D Λ x) (M : ELVWeightProduct D Sc cutoff bound Λ x) :
    elvWeightUnitApp D Sc cutoff bound i Λ h β M ∈ parity (R := k) _ _ 0 := by
  unfold elvWeightUnitApp
  rw [← zero_add (0 : ZMod 2)]
  exact comp_mem (elvBlockAdj_unit_mem D Sc cutoff bound i Λ h β (M β))
    (IsSuperfunctor.map_mem (F := (elvBlockRes D Sc cutoff bound i Λ h β).toFunctor)
      (eqToHom_mem_parity_zero (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M).symm))

theorem elvWeightUnit_mem (M : ELVWeightProduct D Sc cutoff bound Λ x) :
    (elvWeightUnit D Sc cutoff bound i Λ h).app M ∈ parity (R := k) _ _ 0 := fun β =>
  elvWeightUnitApp_mem D Sc cutoff bound i Λ h β M

theorem elvWeightCounit_mem (M : ELVWeightProduct D Sc cutoff bound Λ y) :
    (elvWeightCounit D Sc cutoff bound i Λ h).app M ∈ parity (R := k) _ _ 0 := fun δ => by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change elvWeightCounitComponent D Sc cutoff bound i Λ h M (blockSucc D Λ i h β) ∈ _
    rw [elvWeightCounitComponent_blockSucc, ← zero_add (0 : ZMod 2)]
    exact comp_mem (eqToHom_mem_parity_zero (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β
        ((elvF D Sc cutoff bound i Λ h).obj M)))
      (elvBlockAdj_counit_mem D Sc cutoff bound i Λ h β (M (blockSucc D Λ i h β)))
  · rw [(elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ _).eq_of_src
      ((elvWeightCounit D Sc cutoff bound i Λ h).app M δ) 0]
    exact Submodule.zero_mem _

end Weight
end OddMath.QuiverHecke.ELV
end

end

section

/-! # The actual full-ELV induction/restriction superadjunction

The existing ordinary weight adjunction has even unit and counit. They are
lifted to supernatural transformations and packaged in the actual PiSCat
action target. No local-inverse or factor-family assumption is supplied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The weight-space unit as an even supernatural transformation. -/
def elvActionUnit : 𝟙 _ ⟶ elvE D Sc cutoff bound i Λ h ≫ elvF D Sc cutoff bound i Λ h :=
  SuperNatTrans.ofNatTrans (elvWeightUnit D Sc cutoff bound i Λ h)
    (elvWeightUnit_mem D Sc cutoff bound i Λ h)

/-- The weight-space counit as an even supernatural transformation. -/
def elvActionCounit : elvF D Sc cutoff bound i Λ h ≫ elvE D Sc cutoff bound i Λ h ⟶ 𝟙 _ :=
  SuperNatTrans.ofNatTrans (elvWeightCounit D Sc cutoff bound i Λ h)
    (elvWeightCounit_mem D Sc cutoff bound i Λ h)

/-- Lift an ordinary adjunction with even components to the superadjunction interface. -/
def ordinaryEvenSuperAdjunction
    {A B : PiSCat.{u, u, u + 1} k} (E : A ⟶ B) (F : B ⟶ A)
    (adj : E.toFunctor ⊣ F.toFunctor)
    (hη : ∀ M, adj.unit.app M ∈ parity (R := k) _ _ 0)
    (hε : ∀ N, adj.counit.app N ∈ parity (R := k) _ _ 0) :
    SKM.SuperAdjunction (k := k) E F where
  unit := SuperNatTrans.ofNatTrans adj.unit hη
  counit := SuperNatTrans.ofNatTrans adj.counit hε
  unit_mem := Superfunctor.mem_parity_iff_isHomogeneous.2
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)
  counit_mem := Superfunctor.mem_parity_iff_isHomogeneous.2
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)
  left_triangle := by
    apply Superfunctor.hom_ext_parity
    · intro M
      simp [SuperNatTrans.ofNatTrans, Superfunctor.map, Superfunctor.obj]
    · intro M
      simp [SuperNatTrans.ofNatTrans]
  right_triangle := by
    apply Superfunctor.hom_ext_parity
    · intro N
      simp [SuperNatTrans.ofNatTrans, Superfunctor.map, Superfunctor.obj]
    · intro N
      simp [SuperNatTrans.ofNatTrans]

/-- The actual even induction/restriction adjunction in the PiSCat target. -/
def elvActionAdjunction :
    SKM.SuperAdjunction (k := k) (elvE D Sc cutoff bound i Λ h)
      (elvF D Sc cutoff bound i Λ h) :=
  ordinaryEvenSuperAdjunction (elvE D Sc cutoff bound i Λ h)
    (elvF D Sc cutoff bound i Λ h) (elvWeightAdjunction D Sc cutoff bound i Λ h)
    (elvWeightUnit_mem D Sc cutoff bound i Λ h)
    (elvWeightCounit_mem D Sc cutoff bound i Λ h)

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# The Rouquier mate kernel at one height

Write `A`, `B`, `C` for the deformed cyclotomic algebras at heights `n`, `n + 1`, `n + 2` of
the extended tower, `φ : A → B` and `φ₂ : B → C` for the strand maps of colour `i`, and
`τ ∈ C` for the crossing of the last two `i`-strands. The induction and restriction corners
`P₁ = B e`, `Q₁ = e B`, `P₂ = C e₂`, `Q₂ = e₂ C` are those of `GlobalHeightAdjunction`.

This file constructs the kernel of the Rouquier mate on these corners,
`s : B e ⊗_A e B → e₂ C ⊗_C C e₂`, `x ⊗ y ↦ -(-1)^{p|x|} φ₂(x) τ φ₂(y) ⊗ e₂`,
where `p = |i|`. It is the descended source map `s = -F̄ J` of display (2) in
`docs/Nondegeneracy/DeformedMatrixComparison.md`: `J(x ⊗ y) = (-1)^{p|x|} x ⊗ π^p y` carries
the Koszul sign and `F̄` multiplies through the crossing. The construction uses only the
signed intertwining relation `φ₂(φ r) τ = (-1)^{p|r|} τ φ₂(φ r)` of the crossing
(`heightLastCrossing_intertwines` with `j = i`).

## Main declarations

* `rouquierMateKernel`: the superbimodule morphism `tensor P₁ Q₁ ⟶ tensor Q₂ P₂`.
* `rouquierMateKernel_parity`: it has parity `|i|`.
* `rouquierMateKernel_apply`: its value on homogeneous elementary tensors.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open SuperBimodule
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)

local notation "C₂" => heightAlgebra D Sc a (n + 1 + 1)
local notation "GA" => heightParity D Sc a ha n
local notation "GB" => heightParity D Sc a ha (n + 1)
local notation "GC" => heightParity D Sc a ha (n + 1 + 1)
local notation "φ₁" => heightAppend D Sc a i n
local notation "φ₂" => heightAppend D Sc a i (n + 1)
local notation "τ" => heightLastCrossing D Sc a i i n
local notation "P₁" => heightInductionCorner D Sc i a ha n
local notation "Q₁" => heightRestrictionCorner D Sc i a ha n
local notation "P₂" => heightInductionCorner D Sc i a ha (n + 1)
local notation "Q₂" => heightRestrictionCorner D Sc i a ha (n + 1)
local notation "p" => D.parity i

/-- The algebra element `-φ₂(sgn x) τ φ₂(y)` underlying the mate kernel. -/
def rouquierMateKernelElement (x : (P₁).toSVec) (y : (Q₁).toSVec) : C₂ :=
  -(φ₂ ((P₁).toSVec.sgn p x).val * τ * φ₂ y.val)

theorem rouquierMateKernelElement_left (x : (P₁).toSVec) (y : (Q₁).toSVec) :
    φ₂ 1 * rouquierMateKernelElement D Sc i a ha n x y =
      rouquierMateKernelElement D Sc i a ha n x y := by
  unfold rouquierMateKernelElement
  rw [mul_neg, ← mul_assoc, ← mul_assoc, ← map_mul, one_mul]

/-- The kernel element as an element of the upper restriction corner `e₂ C`. -/
def rouquierMateKernelCorner (x : (P₁).toSVec) (y : (Q₁).toSVec) : (Q₂).toSVec :=
  ⟨rouquierMateKernelElement D Sc i a ha n x y, rouquierMateKernelElement_left D Sc i a ha n x y⟩

/-- The kernel is bilinear in the two corner factors. -/
def rouquierMateKernelBi : (P₁).toSVec →ₗ[k] (Q₁).toSVec →ₗ[k] (Q₂).toSVec where
  toFun x :=
    { toFun := fun y => rouquierMateKernelCorner D Sc i a ha n x y
      map_add' := fun y z => by
        apply Subtype.ext
        change -(_ * _ * φ₂ (y.val + z.val)) = -(_ * _ * φ₂ y.val) + -(_ * _ * φ₂ z.val)
        rw [map_add, mul_add, neg_add]
      map_smul' := fun c y => by
        apply Subtype.ext
        change -(_ * _ * φ₂ (c • y.val)) = c • -(_ * _ * φ₂ y.val)
        rw [map_smul, mul_smul_comm, smul_neg] }
  map_add' x y := by
    ext z
    apply Subtype.ext
    change -(φ₂ ((P₁).toSVec.sgn p (x + y)).val * _ * _) =
      -(φ₂ ((P₁).toSVec.sgn p x).val * _ * _) + -(φ₂ ((P₁).toSVec.sgn p y).val * _ * _)
    rw [map_add]
    change -(φ₂ (((P₁).toSVec.sgn p x).val + ((P₁).toSVec.sgn p y).val) * _ * _) = _
    rw [map_add, add_mul, add_mul, neg_add]
  map_smul' c x := by
    ext z
    apply Subtype.ext
    change -(φ₂ ((P₁).toSVec.sgn p (c • x)).val * _ * _) =
      c • -(φ₂ ((P₁).toSVec.sgn p x).val * _ * _)
    rw [map_smul]
    change -(φ₂ (c • ((P₁).toSVec.sgn p x).val) * _ * _) = _
    rw [map_smul, smul_mul_assoc, smul_mul_assoc, smul_neg]

private theorem sgn_action {q : ZMod 2} {f : (P₁).toSVec ⟶ (P₁).toSVec}
    (hf : f ∈ SVec.parityHom (P₁).toSVec (P₁).toSVec q) (x : (P₁).toSVec) :
    (P₁).toSVec.sgn p (f x) = sign k (q * p) • f ((P₁).toSVec.sgn p x) :=
  LinearMap.congr_fun (SVec.sgn_comp_of_mem hf p) x

omit [Fintype I] in
private theorem parity_mul_self : p * p = p := by
  rcases parity_eq_zero_or_one (D.parity i) with h | h <;> rw [h] <;> decide

/-- The kernel is balanced over the lower algebra `A`: the Koszul sign of `J` cancels the
sign of the crossing intertwiner. -/
theorem rouquierMateKernel_balance (x : (P₁).toSVec) (r : heightAlgebra D Sc a n)
    (y : (Q₁).toSVec) :
    rouquierMateKernelBi D Sc i a ha n ((P₁).ract r x) y =
      rouquierMateKernelBi D Sc i a ha n x ((Q₁).lact r y) := by
  induction r using SuperBimodule.alg_induction_on GA with
  | zero => simp
  | add r s hr hs =>
    rw [map_add, map_add, SVec.add_apply, SVec.add_apply, map_add, LinearMap.add_apply, map_add,
      hr, hs]
  | hom q r hr =>
    have h := sgn_action D Sc i a ha n ((P₁).ract_mem q r hr) x
    apply Subtype.ext
    change -(φ₂ ((P₁).toSVec.sgn p ((P₁).ract r x)).val * τ * φ₂ y.val) =
      -(φ₂ ((P₁).toSVec.sgn p x).val * τ * φ₂ (φ₁ r * y.val))
    rw [h]
    change -(φ₂ (sign k (q * p) • (((P₁).toSVec.sgn p x).val * φ₁ r)) * τ * φ₂ y.val) = _
    have hi := heightLastCrossing_intertwines D Sc a i i ha n hr
    rw [map_smul, map_mul, smul_mul_assoc, smul_mul_assoc, mul_assoc _ (φ₂ (φ₁ r)), hi,
      parity_mul_self, map_mul, mul_smul_comm, smul_mul_assoc, Supercategory.sign_mul, Int.cast_smul_eq_zsmul,
      koszulSign_smul_smul, mul_assoc, mul_assoc, mul_assoc]

/-- The identification `z ↦ z ⊗ e₂` of `e₂ C` with elements of `e₂ C ⊗_C C e₂`. -/
def rouquierMateKernelTarget : (Q₂).toSVec →ₗ[k] (tensor Q₂ P₂).toSVec where
  toFun z := btmul Q₂ P₂ z (heightInductionCornerIdempotent D Sc i a ha (n + 1))
  map_add' z w := btmul_add_left _ _ z w _
  map_smul' c z := btmul_smul_left _ _ c z _

/-- The linear map on the balanced tensor product. -/
def rouquierMateKernelLinear : (tensor P₁ Q₁).toSVec →ₗ[k] (tensor Q₂ P₂).toSVec :=
  rouquierMateKernelTarget D Sc i a ha n ∘ₗ
    tensorLift (rouquierMateKernelBi D Sc i a ha n) (rouquierMateKernel_balance D Sc i a ha n)

@[simp] theorem rouquierMateKernelLinear_btmul (x : (P₁).toSVec) (y : (Q₁).toSVec) :
    rouquierMateKernelLinear D Sc i a ha n (btmul P₁ Q₁ x y) =
      btmul Q₂ P₂ (rouquierMateKernelCorner D Sc i a ha n x y)
        (heightInductionCornerIdempotent D Sc i a ha (n + 1)) := by
  change rouquierMateKernelTarget D Sc i a ha n
    (tensorLift (rouquierMateKernelBi D Sc i a ha n) _ (btmul P₁ Q₁ x y)) = _
  rw [tensorLift_btmul]
  rfl

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The dotted unit, dotted counit and Rouquier mate through the kernels, at one height

Write `A`, `B`, `C` for the deformed cyclotomic algebras at heights `n`, `n + 1`, `n + 2`,
`P = B e`, `Q = e B` for the induction and restriction corners of colour `i` at height `n`,
`P₂`, `Q₂` for those at height `n + 1`, `x` for the last dot and `p = |i|`. The functor-level
data of the Rouquier interface, evaluated on a module `M`, factor through the kernels of
`RouquierCupCapKernel` and `RouquierMateKernel` tensored with `M`:

* the `m`-th power of the dot on `P` (`heightInductionDotPow`) is
  `y ↦ (-1)^{m p |y|} d_m y x^m`, with `d_m = (-1)^{p (m choose 2)}` (`rouquierDotSign`);
* the dotted unit `M → Q ⊗ P ⊗ M`, the unit followed by the `m`-th dot power, is
  `d_m` times the dotted cup `j_m ⊗ M` (`heightSuperUnit_dotPow`);
* the dotted counit `P ⊗ Q ⊗ M → M`, the `m`-th dot power followed by the counit, is
  `d_m` times the dotted cap `κ_m ⊗ M` (`heightDotPow_superCounit`);
* the mate `P ⊗ Q ⊗ M → Q₂ ⊗ P₂ ⊗ M`, unit at height `n + 1`, then the crossing `ψ`, then the
  counit at height `n`, is minus the mate kernel `s ⊗ M` (`heightRouquierMate_eq`). For the
  signed crossing `-ψ` of `globalRouquierData` it is `s ⊗ M`.

These are the height-level forms of the identifications `u_m = d_m j_m`, `c_m = d_m κ_m`
and of the mate kernel in display (2)/(4) of `docs/Nondegeneracy/DeformedMatrixComparison.md`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open SuperBimodule
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v

/-- The normalizing sign `d_m = (-1)^{p (m choose 2)}` of the `m`-th dot power. -/
def rouquierDotSign (p : ZMod 2) : ℕ → ℤ
  | 0 => 1
  | m + 1 => rouquierDotSign p m * koszulSign p (m : ZMod 2)

variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)


/-! ### Powers of the dot on the induction corner -/

/-! ### The dotted unit and the dotted counit -/

/-! ### The Rouquier mate -/

end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-!
# The weight-level Rouquier mate, dotted units and dotted counits through the kernels

`RouquierKernelComparison` identifies, at one height, the dotted unit, the dotted counit and
the Rouquier mate of the cyclotomic action with the dotted cup `j_m ⊗ M`, the dotted cap
`κ_m ⊗ M` and the mate kernel `s ⊗ M`. This file carries these identifications through the
content blocks and the weight-indexed products of `globalRouquierData`, the data entering the
local inversion criterion of Kang–Kashiwara–Oh (KKO I, arXiv:1206.5933v2) as in
`docs/Nondegeneracy/DeformedMatrixComparison.md`, displays (2) and (4).

Write `d_m = rouquierDotSign p m`, `p = |i|`. At the content level:

* `heightContentMate`: the content mate (unit, crossing, counit, with all height transports)
  is minus `contentMateKernel`, the mate kernel tensored with the module;
* `contentUnit_dotPow`: the unit followed by the `m`-th dot power is `d_m` times
  `contentCupKernel`;
* `contentDotPow_counit`: the `m`-th dot power followed by the counit is `d_m` times
  `contentCapKernel`.

At the weight level, for a block `β` and its successor `blockSucc β`:

* `globalRouquierMate_app_blockSucc`: the component of the weight-level `rouquierMate` of the
  signed crossing is the transported `contentMateKernel`, up to the canonical `eqToHom`s;
* `globalActionDotPow_app_blockSucc`: the `m`-th power of the weight-level dot is the
  transported content dot power;
* `globalDottedCounit_app_blockSucc`: the dotted counit is `d_m` times the transported
  `contentCapKernel`;
* `globalDottedUnit_app`: the dotted unit is `d_m` times `contentCupKernel`, followed by the
  canonical identification of objects.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I] [DecidableEq I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

section SCatEven
variable {A B : SCat k}

omit [Fintype I] [DecidableEq I] in
@[simp] theorem scat_whiskerLeft_id {C : SCat k} (F : A ⟶ B) (G : B ⟶ C) :
    F ◁ 𝟙 G = 𝟙 (F ≫ G) := by
  apply SCat.hom_ext <;> intro Z <;> rfl

omit [Fintype I] [DecidableEq I] in
@[simp] theorem scat_id_whiskerRight {C : SCat k} (F : A ⟶ B) (G : B ⟶ C) :
    𝟙 F ▷ G = 𝟙 (F ≫ G) := by
  apply SCat.hom_ext <;> intro Z <;> simp

omit [Fintype I] [DecidableEq I] in
/-- The Rouquier mate in `𝔖ℭ𝔞𝔱` with even unit and counit, componentwise: the unit, then the
crossing under `F₂`, then the counit under `F₂ E₂`. -/
theorem scat_rouquierMate_app {a b c : SCat k} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c}
    {F₂ : c ⟶ b} (A₁ : SKM.SuperAdjunction (k := k) E₁ F₁)
    (A₂ : SKM.SuperAdjunction (k := k) E₂ F₂) (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (hu : ∀ Z, A₂.unit.app 1 Z = 0) (hc : ∀ Z, A₁.counit.app 1 Z = 0) (r : ZMod 2)
    (Z : b.carrier) :
    (SKM.rouquierMate A₁ A₂ t).app r Z =
      A₂.unit.app 0 (Superfunctor.obj (F₁ ≫ E₁) Z) ≫
        Superfunctor.map F₂ (t.app r (Superfunctor.obj F₁ Z)) ≫
          Superfunctor.map F₂ (Superfunctor.map E₂ (A₁.counit.app 0 Z)) := by
  rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) r with rfl | rfl
  · simp [SKM.rouquierMate, hu, hc]
  · simp [SKM.rouquierMate, hu, hc]

end SCatEven

section Content
variable (i : I)

/-! ### Dotted units and counits on content blocks -/

end Content

section Weight
variable (i : I) (Λ : X) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

end Weight
end OddMath.QuiverHecke.CyclotomicAction
end

end

section

/-! # The old module adjunction and its ordered crossing mate

The module category uses its canonical vector-parity structure, the
adjunction is the existing balanced-induction adjunction, and the crossing
is the signed double-induction crossing. The generic SCat mate expansion
is applied to these constructed maps. This remains an old/untruncated
construction; coefficient-truncated exact-content transport is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- One underlying category record is shared by both ambient views. -/
def oldModuleCategory : SCat.{u, u, u + 1} k :=
  SCat.of k (Superfunctor k (OldCategory D Sc cutoff) (SVec k))

def oldModulePiCategory : PiSCat.{u, u, u + 1} k where
  toSCat := oldModuleCategory D Sc cutoff
  pi := by
    change PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    exact supermodulePiSupercategory (k := k) (C := OldCategory D Sc cutoff)

def oldInduction (i : I) :
    oldModuleCategory D Sc cutoff ⟶ oldModuleCategory D Sc cutoff :=
  show Superfunctor k (Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) from
      ⟨BalancedInduction.induction (k := k) (append D Sc cutoff i)⟩

def oldRestriction (i : I) :
    oldModuleCategory D Sc cutoff ⟶ oldModuleCategory D Sc cutoff :=
  show Superfunctor k (Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) from
      ⟨BalancedInduction.restriction (k := k) (append D Sc cutoff i)⟩

def oldInductionPi (i : I) :
    oldModulePiCategory D Sc cutoff ⟶ oldModulePiCategory D Sc cutoff :=
  oldInduction D Sc cutoff i

def oldRestrictionPi (i : I) :
    oldModulePiCategory D Sc cutoff ⟶ oldModulePiCategory D Sc cutoff :=
  oldRestriction D Sc cutoff i

def oldAppendPiAdjunction (i : I) :
    SKM.SuperAdjunction (k := k) (B := PiSCat.{u, u, u + 1} k)
      (oldInductionPi D Sc cutoff i) (oldRestrictionPi D Sc cutoff i) :=
  ordinaryEvenSuperAdjunction (k := k) (oldInductionPi D Sc cutoff i) (oldRestrictionPi D Sc cutoff i)
    (BalancedInduction.adjunction (append D Sc cutoff i))
    (BalancedInduction.adjunctionUnit_mem (append D Sc cutoff i))
    (BalancedInduction.adjunctionCounit_mem (append D Sc cutoff i))

/-- Forgetting Π changes none of the constructed adjunction maps or triangles. -/
def oldAppendAdjunction (i : I) :
    SKM.SuperAdjunction (k := k) (B := SCat.{u, u, u + 1} k)
      (a := oldModuleCategory D Sc cutoff) (b := oldModuleCategory D Sc cutoff)
      (oldInduction D Sc cutoff i) (oldRestriction D Sc cutoff i) where
  unit := (oldAppendPiAdjunction D Sc cutoff i).unit
  counit := (oldAppendPiAdjunction D Sc cutoff i).counit
  unit_mem := (oldAppendPiAdjunction D Sc cutoff i).unit_mem
  counit_mem := (oldAppendPiAdjunction D Sc cutoff i).counit_mem
  left_triangle := (oldAppendPiAdjunction D Sc cutoff i).left_triangle
  right_triangle := (oldAppendPiAdjunction D Sc cutoff i).right_triangle

theorem oldAppendAdjunction_unit_app (i : I) (q : ZMod 2)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (oldAppendAdjunction D Sc cutoff i).unit.app q M =
      if q = 0 then (BalancedInduction.adjunctionUnit (append D Sc cutoff i)).app M else 0 := rfl

theorem oldAppendAdjunction_counit_app (i : I) (q : ZMod 2)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (oldAppendAdjunction D Sc cutoff i).counit.app q M =
      if q = 0 then (BalancedInduction.adjunctionCounit (append D Sc cutoff i)).app M else 0 := rfl

def oldSignedCross (i : I) :
    oldInduction D Sc cutoff i ≫ oldInduction D Sc cutoff i ⟶
      oldInduction D Sc cutoff i ≫ oldInduction D Sc cutoff i :=
  signedEqualInductionCross D Sc cutoff i

/-- The ordered cup-crossing-cap mate of the constructed adjunction and crossing. -/
def oldModuleMate (i : I) :
    oldRestriction D Sc cutoff i ≫ oldInduction D Sc cutoff i ⟶
      oldInduction D Sc cutoff i ≫ oldRestriction D Sc cutoff i :=
  SKM.rouquierMate (k := k) (B := SCat.{u, u, u + 1} k) (oldAppendAdjunction D Sc cutoff i) (oldAppendAdjunction D Sc cutoff i)
    (oldSignedCross D Sc cutoff i)

/-- The existing generic mate expansion, specialized without an adjunction premise. -/
theorem oldModuleMate_app (i : I) (r : ZMod 2)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (oldModuleMate D Sc cutoff i).app r M =
      (BalancedInduction.adjunctionUnit (append D Sc cutoff i)).app
        ((BalancedInduction.induction (k := k) (append D Sc cutoff i)).obj
          ((BalancedInduction.restriction (k := k) (append D Sc cutoff i)).obj M)) ≫
        (BalancedInduction.restriction (k := k) (append D Sc cutoff i)).map
          ((signedEqualInductionCross D Sc cutoff i).app r
            ((BalancedInduction.restriction (k := k) (append D Sc cutoff i)).obj M)) ≫
        (BalancedInduction.restriction (k := k) (append D Sc cutoff i)).map
          ((BalancedInduction.induction (k := k) (append D Sc cutoff i)).map
            ((BalancedInduction.adjunctionCounit (append D Sc cutoff i)).app M)) := by
  have h := CyclotomicAction.scat_rouquierMate_app (k := k)
    (a := oldModuleCategory D Sc cutoff) (b := oldModuleCategory D Sc cutoff)
    (c := oldModuleCategory D Sc cutoff)
    (E₁ := oldInduction D Sc cutoff i) (F₁ := oldRestriction D Sc cutoff i)
    (E₂ := oldInduction D Sc cutoff i) (F₂ := oldRestriction D Sc cutoff i)
    (oldAppendAdjunction D Sc cutoff i) (oldAppendAdjunction D Sc cutoff i)
    (oldSignedCross D Sc cutoff i)
    (fun Z => by simp only [oldAppendAdjunction_unit_app, one_ne_zero, ↓reduceIte])
    (fun Z => by simp only [oldAppendAdjunction_counit_app, one_ne_zero, ↓reduceIte]) r M
  exact h

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Rectangular mate components between four weight spaces

Brundan–Ellis (1.12) uses the selected crossing between the two orders
of different induction functors, bent by two j-adjunctions at different
weights. The cup and cap are even; the middle crossing may be odd.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.SKM
universe u
variable {k : Type u} [CommRing k]
  {a b c d : PiSCat.{u,u,u + 1} k}
  {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₃ : c ⟶ d} {F₃ : d ⟶ c}

/-- All four corner categories remain independent in the component formula. -/
theorem rectangularMate_piscat_app
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₃ : SuperAdjunction (k := k) E₃ F₃)
    (g : a ⟶ c) (h : b ⟶ d) (z : g ≫ E₃ ⟶ E₁ ≫ h)
    (hu : ∀ Z, A₃.unit.app 1 Z = 0) (hc : ∀ Z, A₁.counit.app 1 Z = 0)
    (r : ZMod 2) (Z : b.carrier) :
    (rectangularMate A₁ A₃ g h z).app r Z =
      A₃.unit.app 0 (g.obj (F₁.obj Z)) ≫
        F₃.map (z.app r (F₁.obj Z)) ≫ F₃.map (h.map (A₁.counit.app 0 Z)) := by
  rw [rectangularMate_eq]
  rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp [PiSCat.whiskerLeft_def, PiSCat.whiskerRight_def,
      Superfunctor.whiskerLeft_app, Superfunctor.whiskerRight_app, hu, hc]

/-- Even bending maps retain the complete crossing degree at all four corners. -/
theorem rectangularMate_piscat_mem
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₃ : SuperAdjunction (k := k) E₃ F₃)
    (g : a ⟶ c) (h : b ⟶ d) {p : ZMod 2} (z : g ≫ E₃ ⟶ E₁ ≫ h)
    (hz : z ∈ parity (R := k) _ _ p) :
    rectangularMate A₁ A₃ g h z ∈ parity (R := k) _ _ p := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  funext Z
  rw [rectangularMate_piscat_app A₁ A₃ g h z
    (fun W => Superfunctor.app_eq_zero_of_mem A₃.unit_mem (by decide) W)
    (fun W => Superfunctor.app_eq_zero_of_mem A₁.counit_mem (by decide) W)]
  rw [Superfunctor.app_eq_zero_of_mem hz hq]
  simp only [Superfunctor.map, CategoryTheory.Functor.map_zero,
    CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]
  rfl

end OddMath.SKM
end

end

section

/-! # Rouquier cup-crossing-cap in the PiSCat action target

Brundan–Ellis (1.13)–(1.14) uses the local rank-one Rouquier mate.
Its given component formula agrees with the rectangular cup-crossing-cap
used in the content matrix charts. Units and counits remain those of
the two specified adjunctions.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.SKM
universe u
variable {k : Type u} [CommRing k] {A B C : PiSCat.{u,u,u + 1} k}
  {E₁ : A ⟶ B} {F₁ : B ⟶ A} {E₂ : B ⟶ C} {F₂ : C ⟶ B}
  (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
  (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)

/-- The prescribed Rouquier mate keeps the upper cup and lower cap at their distinct weight corners. -/
theorem rouquierMate_piscat_app (p : ZMod 2) (Z : B.carrier) :
    (rouquierMate A₁ A₂ t).app p Z =
      A₂.unit.app 0 (E₁.obj (F₁.obj Z)) ≫
        F₂.map (t.app p (F₁.obj Z)) ≫ F₂.map (E₂.map (A₁.counit.app 0 Z)) := by
  have hu := Superfunctor.app_eq_zero_of_mem A₂.unit_mem (by decide : (1 : ZMod 2) ≠ 0)
  have hc := Superfunctor.app_eq_zero_of_mem A₁.counit_mem (by decide : (1 : ZMod 2) ≠ 0)
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [rouquierMate, PiSCat.whiskerLeft_def, PiSCat.whiskerRight_def,
      Superfunctor.whiskerLeft_app, Superfunctor.whiskerRight_app, hu, hc]

/-- Both chosen mate conventions give the same whole supernatural map in PiSCat. -/
theorem rouquierMate_piscat_eq_rectangular :
    rouquierMate A₁ A₂ t = rectangularMate A₁ A₂ E₁ E₂ t := by
  apply Superfunctor.hom_ext
  intro p Z
  exact (rouquierMate_piscat_app A₁ A₂ t p Z).trans
    (rectangularMate_piscat_app A₁ A₂ E₁ E₂ t
      (Superfunctor.app_eq_zero_of_mem A₂.unit_mem (by decide : (1 : ZMod 2) ≠ 0))
      (Superfunctor.app_eq_zero_of_mem A₁.counit_mem (by decide : (1 : ZMod 2) ≠ 0)) p Z).symm

end OddMath.SKM
end

end
