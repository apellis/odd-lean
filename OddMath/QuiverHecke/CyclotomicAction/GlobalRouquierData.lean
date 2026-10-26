/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightCross

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

theorem contentCross_square (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ x₂)
    (hc : {i} + ({i} + β.1) = ε.1) (M : GlobalContentModules D Sc a ha β.1) :
    (contentCross D Sc a ha i i Λ β ε hc).app (D.parity i * D.parity i) M ≫
      (contentCross D Sc a ha i i Λ β ε hc).app (D.parity i * D.parity i) M = 0 := by
  change (heightContentCast D Sc a ha (card_of_add₂ i i hc) rfl).map
      ((heightBlockCross D Sc a ha i i β.1.card β.1 ε.1 hc).app _ M) ≫
    (heightContentCast D Sc a ha (card_of_add₂ i i hc) rfl).map
      ((heightBlockCross D Sc a ha i i β.1.card β.1 ε.1 hc).app _ M) = 0
  rw [← Functor.map_comp]
  have hz : (heightBlockCross D Sc a ha i i β.1.card β.1 ε.1 hc).app
      (D.parity i * D.parity i) M ≫
      (heightBlockCross D Sc a ha i i β.1.card β.1 ε.1 hc).app (D.parity i * D.parity i) M = 0 :=
    InducedCategory.hom_ext (heightSuperInductionCrossing_square D Sc a ha i β.1.card M.obj)
  rw [hz]
  exact Functor.map_zero _ _ _

/-- **The same-colour weight crossing squares to zero.** -/
theorem globalActionCross_square :
    globalActionCross D Sc a ha i i Λ h₁ h₂ h₁ h₂ ≫
      globalActionCross D Sc a ha i i Λ h₁ h₂ h₁ h₂ = 0 := by
  refine superTrans_comp_eq_zero (globalWeightCross_homogeneous D Sc a ha i i Λ h₁ h₂ h₁ h₂)
    (globalWeightCross_homogeneous D Sc a ha i i Λ h₁ h₂ h₁ h₂) fun M => ?_
  funext ε
  change globalWeightCrossComponent D Sc a ha i i Λ h₁ h₂ h₁ h₂ _ M ε ≫
    globalWeightCrossComponent D Sc a ha i i Λ h₁ h₂ h₁ h₂ _ M ε = 0
  by_cases hε : ∃ β, blockSucc₂ D i i Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [globalWeightCrossComponent_of D Sc a ha i i Λ h₁ h₂ h₁ h₂ _ M β ε hβ]
    unfold globalWeightCrossVia
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% (contentCross_square D Sc a ha Λ i β ε (congrArg Subtype.val hβ) (M β))]
    simp
  · exact (globalEFunctor_comp_isZero D Sc a ha i i Λ h₁ h₂ ε hε M).eq_of_src _ _

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

theorem globalActionSignedCross_mem :
    globalActionSignedCross D Sc a ha Λ i j h₁ h₂ h₃ h₄ ∈
      parity (R := k) _ _ (D.parity i * D.parity j) := by
  unfold globalActionSignedCross
  split
  · exact neg_mem (globalActionCross_mem D Sc a ha i j Λ h₁ h₂ h₃ h₄)
  · exact globalActionCross_mem D Sc a ha i j Λ h₁ h₂ h₃ h₄

theorem globalActionSignedCross_square {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁)
    (h₂ : x₁ + D.α i = x₂) :
    globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂ ≫
      globalActionSignedCross D Sc a ha Λ i i h₁ h₂ h₁ h₂ = 0 := by
  simp only [globalActionSignedCross, ite_true, Preadditive.neg_comp, Preadditive.comp_neg,
    neg_neg]
  exact globalActionCross_square D Sc a ha Λ i h₁ h₂

end Signed

/-- **Rouquier data on cyclotomic weight spaces**: weight-space induction, the dot and the
signed crossing in the supercategory of supercategories. -/
def globalRouquierData [DecidableEq I] :
    SKM.RouquierData (k := k) (B := cyclotomicActionTarget (k := k)) D where
  obj x := globalWeightSpace D Sc a ha Λ x
  E i _ _ h := globalActionE D Sc a ha i Λ h
  dot i _ _ h := globalActionDot D Sc a ha i Λ h
  dot_mem i _ _ h := globalActionDot_mem D Sc a ha i Λ h
  cross i j _ _ _ _ h₁ h₂ h₃ h₄ := globalActionSignedCross D Sc a ha Λ i j h₁ h₂ h₃ h₄
  cross_mem i j _ _ _ _ h₁ h₂ h₃ h₄ := globalActionSignedCross_mem D Sc a ha Λ i j h₁ h₂ h₃ h₄

theorem globalRouquierData_square [DecidableEq I] (i : I) {x₀ x₁ x₂ : X}
    (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) :
    (globalRouquierData D Sc a ha Λ).cross i i h₁ h₂ h₁ h₂ ≫
      (globalRouquierData D Sc a ha Λ).cross i i h₁ h₂ h₁ h₂ = 0 :=
  globalActionSignedCross_square D Sc a ha Λ i h₁ h₂

end OddMath.QuiverHecke.CyclotomicAction
