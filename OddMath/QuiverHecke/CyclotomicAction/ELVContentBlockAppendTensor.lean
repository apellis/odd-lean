/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendTensor

/-! # Tensor formula for truncated full-content append comparison

For Brundan–Ellis (1.12), the selected append extension chart flattens
literal nested quotient coefficients and inserts the canonical inclusion
unit. Common upper content is explicit and coefficient parity is unrestricted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : B ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
private def blockInsertionLinear (M : Superfunctor k C (SVec k)) (w : E) :
    Obj (J ⋙ K) M.toFunctor w →ₗ[k] Obj K (induced J M).toFunctor w :=
  ((inductionComp J K).inv.app M).total w
private theorem blockInsertionLinear_tensor (M : Superfunctor k C (SVec k))
    (s : C) (w : E) (a : K.obj (J.obj s) ⟶ w) (b : M.obj s) :
    blockInsertionLinear J K M w (tensor (J ⋙ K) M.toFunctor s a b) =
      inductionInsertedTensor J K M s w a b :=
  inductionComp_inv_total_tensor J K M s w a b
end OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (σ : List I) (γ : Multiset I) (hσ : β + (σ : Multiset I) = γ)
local notation "J" => contentAppendTo D Sc cutoff N β σ γ hσ
local notation "P" => contentInclusion D Sc cutoff N β
local notation "Q" => contentInclusion D Sc cutoff N γ
local notation "A" => truncatedAppend D Sc cutoff N σ

/-- The chosen chart uses the two specified induction composition comparisons. -/
theorem contentAppendToExtensionIso_hom (M : ContentModules D Sc cutoff N β) :
    (contentAppendToExtensionIso D Sc cutoff N β σ γ hσ).hom.app M =
      (BalancedInduction.inductionComp J Q).hom.app M ≫
        (BalancedInduction.inductionComp P A).inv.app M := by
  have hm : (BalancedInduction.inductionFunctorIsoOfEq (J ⋙ Q) (P ⋙ A)
      (contentAppendTo_inclusion D Sc cutoff N β σ γ hσ)).hom.app M = 𝟙 _ := rfl
  simp only [contentAppendToExtensionIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, hm, Category.id_comp]

private theorem contentAppendToInsertion_tensor (M : ContentModules D Sc cutoff N β)
    (s : ContentCategory D Sc cutoff N β) (w : TruncatedCategory D Sc cutoff N)
    (a : (A).obj s.obj ⟶ w) (b : M.obj s) :
    BalancedInduction.blockInsertionLinear P A M w
      (BalancedInduction.tensor (P ⋙ A) M.toFunctor s a b) =
      BalancedInduction.inductionInsertedTensor P A M s w a b :=
  BalancedInduction.blockInsertionLinear_tensor P A M s w a b

/-- Entire quotient arrows flatten unchanged through the selected content chart. -/
theorem contentAppendToExtensionIso_tensor (M : ContentModules D Sc cutoff N β)
    (s : ContentCategory D Sc cutoff N β) (t : ContentCategory D Sc cutoff N γ)
    (w : TruncatedCategory D Sc cutoff N) (h : t.obj ⟶ w)
    (g : (A).obj s.obj ⟶ t.obj) (b : M.obj s) :
    ((contentAppendToExtensionIso D Sc cutoff N β σ γ hσ).hom.app M).total w
      (BalancedInduction.tensor Q (BalancedInduction.induced J M).toFunctor t h
        (BalancedInduction.tensor J M.toFunctor s g b)) =
      BalancedInduction.inductionInsertedTensor P A M s w (g ≫ h) b := by
  rw [contentAppendToExtensionIso_hom, Superfunctor.comp_total]
  change BalancedInduction.blockInsertionLinear P A M w
    (((BalancedInduction.inductionComp J Q).hom.app M).total w
      (BalancedInduction.tensor Q (BalancedInduction.induced J M).toFunctor t h
        (BalancedInduction.tensor J M.toFunctor s g b))) = _
  have hf := BalancedInduction.inductionComp_hom_total_tensor J Q M s t w h g b
  change ((BalancedInduction.inductionComp J Q).hom.app M).total w
      (BalancedInduction.tensor Q (BalancedInduction.induced J M).toFunctor t h
        (BalancedInduction.tensor J M.toFunctor s g b)) =
      BalancedInduction.tensor (P ⋙ A) M.toFunctor s (g ≫ h) b at hf
  have hFlatten := congrArg (BalancedInduction.blockInsertionLinear P A M w) hf
  have hInsert := contentAppendToInsertion_tensor D Sc cutoff N β σ M s w (g ≫ h) b
  exact hFlatten.trans hInsert
end OddMath.QuiverHecke.ELVOld
