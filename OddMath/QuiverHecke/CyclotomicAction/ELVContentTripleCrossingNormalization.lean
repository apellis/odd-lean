/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairWhiskeredRelations

/-! # Normalization of independently whiskered triple crossings -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem contentTripleLeft_whisker (i j l : I) :
    contentTripleLeft D Sc i j l = crossTwo D Sc i j ▷ (pres D Sc).obj (ob D [l]) := by
  rw [crossTwo, cl_whiskerRight D Sc _ _ [l]
    (by intro g hg; simp only [List.mem_singleton] at hg; subst g; simp [PG.pos, PG.width])]
  rfl

theorem contentTripleRight_whisker (i j l : I) :
    contentTripleRight D Sc i j l = (pres D Sc).obj (ob D [i]) ◁ crossTwo D Sc j l := by
  rw [crossTwo, cl_whiskerLeft]
  rfl

private theorem tripleMap_congr {β γ : Multiset I} {i j l a b c : I}
    (h : β + ([i,j,l] : Multiset I) = γ) (ht : β + ([a,b,c] : Multiset I) = γ)
    {p : ZMod 2}
    {f g : (pres D Sc).obj (ob D [i,j,l]) ⟶ (pres D Sc).obj (ob D [a,b,c])}
    (hf : f ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ p) (hfg : f = g)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentETripleMap D Sc cutoff N h ht hf M z = contentETripleMap D Sc cutoff N h ht hg M z := by
  cases hfg
  rfl

private theorem tripleMap_neg {β γ : Multiset I} {i j l a b c : I}
    (h : β + ([i,j,l] : Multiset I) = γ) (ht : β + ([a,b,c] : Multiset I) = γ)
    {p : ZMod 2}
    {f : (pres D Sc).obj (ob D [i,j,l]) ⟶ (pres D Sc).obj (ob D [a,b,c])}
    (hf : f ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentETripleMap D Sc cutoff N h ht (Submodule.neg_mem _ hf) M z =
      -contentETripleMap D Sc cutoff N h ht hf M z := by
  have hn : BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N h ht (Submodule.neg_mem _ hf)) M z =
      -BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h ht hf) M z := by
    apply BalancedInduction.hom_ext
    intro v a m
    simp only [BalancedInduction.transformLinear_tensor, contentAppendToComponent_neg,
      Preadditive.neg_comp, LinearMap.neg_apply]
    simp only [BalancedInduction.tensor, TensorProduct.neg_tmul, map_neg]
  unfold contentETripleMap
  rw [hn]
  ext x
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearEquiv.coe_coe, map_neg]

/-- Suffix crossing defined by the pair crossing on the first induced module. -/
def contentWhiskeredSuffixCross (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) (ht : β + ([i,l,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ContentETripleSpace D Sc cutoff N β i l j γ ht M z →ₗ[k]
      ContentETripleSpace D Sc cutoff N β i j l γ h M z :=
  ((contentEPairCrossTransform D Sc cutoff N (β + ([i] : Multiset I)) j l γ
    (by rw [add_assoc]; exact h) (by rw [add_assoc]; exact ht)).app
    (D.parity j * D.parity l)
    (BalancedInduction.induced (contentAppend D Sc cutoff N β [i]) M)).total z

theorem contentWhiskeredSuffixCross_comparison (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) (ht : β + ([i,l,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentWhiskeredSuffixCross D Sc cutoff N β i j l γ h ht M z =
      contentETripleMap D Sc cutoff N h ht
        (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D [i]))
          (contentCrossAffine_mem D Sc j l)) M z := by
  unfold contentWhiskeredSuffixCross
  rw [contentEPairCross_total]
  exact (contentETripleMap_suffix_cross D Sc cutoff N β i j l γ h ht _ _ M z).symm
theorem contentWhiskeredPrefixCross_distinct (β : Multiset I) {i j : I} (hij : i ≠ j)
    (l : I) (δ γ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
    (h : β + ([i,j,l] : Multiset I) = γ) (ht : β + ([j,i,l] : Multiset I) = γ)
    (hγ : δ + ([l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentETripleMiddleIso D Sc cutoff N β i j l δ γ hδ h hγ).inv.app M).total z ∘ₗ
        ((contentInductionTo D Sc cutoff N δ [l] γ hγ).map
          ((contentEPairCrossTransform D Sc cutoff N β i j δ
            ((contentPair_sum β i j).trans hδ) ((contentPair_sum β j i).trans hδ')).app
            (D.parity i * D.parity j) M)).total z ∘ₗ
        ((contentETripleMiddleIso D Sc cutoff N β j i l δ γ hδ' ht hγ).hom.app M).total z =
      contentETripleMap D Sc cutoff N h ht (contentTripleLeft_parity D Sc i j l) M z := by
  rw [← contentETripleMap_prefix_cross]
  apply tripleMap_congr
  rw [contentCrossAffine_distinct D Sc i j hij, contentTripleLeft_whisker]

theorem contentWhiskeredSuffixCross_distinct (β : Multiset I) (i : I) {j l : I} (hjl : j ≠ l)
    (γ : Multiset I) (h : β + ([i,j,l] : Multiset I) = γ)
    (ht : β + ([i,l,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentWhiskeredSuffixCross D Sc cutoff N β i j l γ h ht M z =
      contentETripleMap D Sc cutoff N h ht (contentTripleRight_parity D Sc i j l) M z := by
  rw [contentWhiskeredSuffixCross_comparison]
  apply tripleMap_congr
  rw [contentCrossAffine_distinct D Sc j l hjl, contentTripleRight_whisker]

theorem contentWhiskeredPrefixCross_equal (β : Multiset I) (i l : I)
    (δ γ : Multiset I) (hδ : (β + ([i] : Multiset I)) + ([i] : Multiset I) = δ)
    (h : β + ([i,i,l] : Multiset I) = γ) (hγ : δ + ([l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentETripleMiddleIso D Sc cutoff N β i i l δ γ hδ h hγ).inv.app M).total z ∘ₗ
        ((contentInductionTo D Sc cutoff N δ [l] γ hγ).map
          ((contentEPairCrossTransform D Sc cutoff N β i i δ
            ((contentPair_sum β i i).trans hδ) ((contentPair_sum β i i).trans hδ)).app
            (D.parity i * D.parity i) M)).total z ∘ₗ
        ((contentETripleMiddleIso D Sc cutoff N β i i l δ γ hδ h hγ).hom.app M).total z =
      -contentETripleMap D Sc cutoff N h h (contentTripleLeft_parity D Sc i i l) M z := by
  rw [← contentETripleMap_prefix_cross, ← tripleMap_neg]
  apply tripleMap_congr
  rw [contentCrossAffine_equal, MonoidalSupercategory.neg_whiskerRight (R := k), contentTripleLeft_whisker]

theorem contentWhiskeredSuffixCross_equal (β : Multiset I) (j i : I)
    (γ : Multiset I) (h : β + ([j,i,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    contentWhiskeredSuffixCross D Sc cutoff N β j i i γ h h M z =
      -contentETripleMap D Sc cutoff N h h (contentTripleRight_parity D Sc j i i) M z := by
  rw [contentWhiskeredSuffixCross_comparison, ← tripleMap_neg]
  apply tripleMap_congr
  rw [contentCrossAffine_equal, MonoidalSupercategory.whiskerLeft_neg (R := k), contentTripleRight_whisker]

end OddMath.QuiverHecke.ELVOld
