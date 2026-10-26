/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightDot
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightAdjunction

/-!
# The dot on weight-space induction

Ports `globalDot` of `Categorification/KLR/CyclotomicAction/Global.lean`. At
the successor of a block the dot is `globalContentDot`, transported along
`inductionComponent_blockSucc`; at a block without predecessor the induced
component is zero. The result is a supernatural endomorphism of `globalE`,
homogeneous of the colour parity `|i|`: odd colours carry the odd dot. This is
the `dot` field of `RouquierData` on weight spaces.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

section Weight
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The content dot between a block and its successor. -/
abbrev blockDot (β : WeightBlocks D Λ x) :=
  globalContentDot D Sc i a ha (blockSucc_val D Λ i h β).symm

/-- The dot component at a block with a chosen predecessor. -/
def globalWeightDotVia (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (inductionComponent D Sc a ha i Λ h δ).obj M ⟶ (inductionComponent D Sc a ha i Λ h δ).obj M := by
  subst hβ
  exact eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M) ≫
    (blockDot D Sc a ha i Λ h β).app p (M β) ≫
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M).symm

theorem globalWeightDotVia_eq (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x)
    (β β' : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ)
    (hβ' : blockSucc D Λ i h β' = δ) :
    globalWeightDotVia D Sc a ha i Λ h p M β δ hβ =
      globalWeightDotVia D Sc a ha i Λ h p M β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The dot component at a block: through the predecessor, or zero. -/
def globalWeightDotComponent (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x)
    (δ : WeightBlocks D Λ y) :
    (inductionComponent D Sc a ha i Λ h δ).obj M ⟶ (inductionComponent D Sc a ha i Λ h δ).obj M :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    globalWeightDotVia D Sc a ha i Λ h p M hδ.choose δ hδ.choose_spec
  else 0

theorem globalWeightDotComponent_blockSucc (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x)
    (β : WeightBlocks D Λ x) :
    globalWeightDotComponent D Sc a ha i Λ h p M (blockSucc D Λ i h β) =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M) ≫
        (blockDot D Sc a ha i Λ h β).app p (M β) ≫
          eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M).symm := by
  unfold globalWeightDotComponent
  split
  · rename_i hc
    exact globalWeightDotVia_eq D Sc a ha i Λ h p M _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem globalWeightDotComponent_mem (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x)
    (δ : WeightBlocks D Λ y) :
    globalWeightDotComponent D Sc a ha i Λ h p M δ ∈ parity (R := k) _ _ p := by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    rw [globalWeightDotComponent_blockSucc]
    have hm := comp_mem (eqToHom_mem_parity_zero
        (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M))
      (comp_mem ((blockDot D Sc a ha i Λ h β).app_mem p (M β))
        (eqToHom_mem_parity_zero (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M).symm))
    simpa only [zero_add, add_zero] using hm
  · rw [(inductionComponent_isZero D Sc a ha i Λ h δ hδ M).eq_of_src
      (globalWeightDotComponent D Sc a ha i Λ h p M δ) 0]
    exact Submodule.zero_mem _

theorem globalWeightDotComponent_naturality (p : ZMod 2) (β : WeightBlocks D Λ x)
    {M M' : WeightProduct D Sc a ha Λ x} {q : ZMod 2} (f : M ⟶ M')
    (hf : f ∈ parity (R := k) M M' q) :
    (inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).map f ≫
        globalWeightDotComponent D Sc a ha i Λ h p M' (blockSucc D Λ i h β) =
      koszulSign p q • (globalWeightDotComponent D Sc a ha i Λ h p M (blockSucc D Λ i h β) ≫
        (inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [inductionComponent_map_blockSucc, globalWeightDotComponent_blockSucc,
    globalWeightDotComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hn := (blockDot D Sc a ha i Λ h β).naturality p (f β) (hf β)
  rw [← Category.assoc ((blockInd D Sc a ha i Λ h β).map (f β)), Superfunctor.map, hn,
    Linear.smul_comp, Linear.comp_smul, Category.assoc]

/-- **The dot on weight-space induction.** -/
def globalWeightDot :
    SuperNatTrans k (globalEFunctor D Sc a ha i Λ h) (globalEFunctor D Sc a ha i Λ h) where
  app p M δ := globalWeightDotComponent D Sc a ha i Λ h p M δ
  app_mem p M δ := globalWeightDotComponent_mem D Sc a ha i Λ h p M δ
  naturality p M M' q f hf := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact globalWeightDotComponent_naturality D Sc a ha i Λ h p β f hf
    · exact (inductionComponent_isZero D Sc a ha i Λ h δ hδ _).eq_of_src _ _

/-- Only the component of the colour parity is nonzero. -/
theorem globalWeightDot_homogeneous :
    (globalWeightDot D Sc a ha i Λ h).IsHomogeneous (D.parity i) := by
  intro q hq
  funext M
  funext δ
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change globalWeightDotComponent D Sc a ha i Λ h q M (blockSucc D Λ i h β) = 0
    rw [globalWeightDotComponent_blockSucc,
      congrFun (globalContentDot_homogeneous D Sc i a ha (blockSucc_val D Λ i h β).symm q hq)
        (M β)]
    simp
  · exact (inductionComponent_isZero D Sc a ha i Λ h δ hδ M).eq_of_src _ _

/-- The dot as a 2-endomorphism of weight-space induction in the action target. -/
def globalActionDot : globalActionE D Sc a ha i Λ h ⟶ globalActionE D Sc a ha i Λ h :=
  globalWeightDot D Sc a ha i Λ h

/-- The dot has the parity of its colour, including for odd colours. -/
theorem globalActionDot_mem :
    globalActionDot D Sc a ha i Λ h ∈
      parity (R := k) (globalActionE D Sc a ha i Λ h) (globalActionE D Sc a ha i Λ h)
        (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.2 (globalWeightDot_homogeneous D Sc a ha i Λ h)

end Weight

end OddMath.QuiverHecke.CyclotomicAction
