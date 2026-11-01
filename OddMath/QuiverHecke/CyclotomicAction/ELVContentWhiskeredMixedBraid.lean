/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleCrossingNormalization
import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleDots

/-! # Mixed braid with explicit intermediate content

Brundan–Ellis Definition 1.5 (1.9). Independent pair crossings are induced
through explicitly supplied common intermediate contents. Keeping those
contents abstract makes the endpoint types agree with the existing comparison
theorems without expanding computed multiset transports. The correction uses
the independent single-letter dots and the original scalar parameters.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Congruence for composition with the ground ring fixed. This avoids
higher-order inference of semilinear composition on nested module carriers. -/
theorem contentLinear_comp_congr
    {A B C : Type u} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C]
    {f f' : B →ₗ[k] A} {g g' : C →ₗ[k] B}
    (hf : f = f') (hg : g = g') : f.comp g = f'.comp g' := by
  cases hf
  cases hg
  rfl

def contentWhiskeredPathIij (β : Multiset I) (i j : I) (δ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([i] : Multiset I) = δ)
    (hγ : δ + ([j] : Multiset I) = β + ([i,j,i] : Multiset I))
    (h : β + ([i,i,j] : Multiset I) = β + ([i,j,i] : Multiset I))
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M z) :=
  (contentWhiskeredSuffixCross D Sc cutoff N β i j i _ rfl h M z).comp
    ((((contentETripleMiddleIso D Sc cutoff N β i i j δ _ hδ h hγ).inv.app M).total z ∘ₗ
      ((contentInductionTo D Sc cutoff N δ [j] _ hγ).map
        ((contentEPairCrossTransform D Sc cutoff N β i i δ
          ((contentPair_sum β i i).trans hδ) ((contentPair_sum β i i).trans hδ)).app
          (D.parity i * D.parity i) M)).total z ∘ₗ
      ((contentETripleMiddleIso D Sc cutoff N β i i j δ _ hδ h hγ).hom.app M).total z).comp
      (contentWhiskeredSuffixCross D Sc cutoff N β i i j _ h rfl M z))

def contentWhiskeredPathJii (β : Multiset I) (i j : I) (δ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
    (hγ : δ + ([i] : Multiset I) = β + ([i,j,i] : Multiset I))
    (h : β + ([j,i,i] : Multiset I) = β + ([i,j,i] : Multiset I))
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M z) :=
  (((contentETripleMiddleIso D Sc cutoff N β i j i δ _ hδ rfl hγ).inv.app M).total z ∘ₗ
    ((contentInductionTo D Sc cutoff N δ [i] _ hγ).map
      ((contentEPairCrossTransform D Sc cutoff N β i j δ
        ((contentPair_sum β i j).trans hδ) ((contentPair_sum β j i).trans hδ')).app
        (D.parity i * D.parity j) M)).total z ∘ₗ
    ((contentETripleMiddleIso D Sc cutoff N β j i i δ _ hδ' h hγ).hom.app M).total z).comp
      ((contentWhiskeredSuffixCross D Sc cutoff N β j i i _ h h M z).comp
        (((contentETripleMiddleIso D Sc cutoff N β j i i δ _ hδ' h hγ).inv.app M).total z ∘ₗ
          ((contentInductionTo D Sc cutoff N δ [i] _ hγ).map
            ((contentEPairCrossTransform D Sc cutoff N β j i δ
              ((contentPair_sum β j i).trans hδ') ((contentPair_sum β i j).trans hδ)).app
              (D.parity j * D.parity i) M)).total z ∘ₗ
          ((contentETripleMiddleIso D Sc cutoff N β i j i δ _ hδ rfl hγ).hom.app M).total z))

theorem contentWhiskeredPathIij_eq (β : Multiset I) {i j : I} (hij : i ≠ j)
    (δ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([i] : Multiset I) = δ)
    (hγ : δ + ([j] : Multiset I) = β + ([i,j,i] : Multiset I))
    (h : β + ([i,i,j] : Multiset I) = β + ([i,j,i] : Multiset I))
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    contentWhiskeredPathIij D Sc cutoff N β i j δ hδ hγ h M z =
      contentETriplePathIij D Sc cutoff N β i j M z :=
  contentLinear_comp_congr (k := k)
    (contentWhiskeredSuffixCross_distinct D Sc cutoff N β i hij.symm _ rfl h M z)
    (contentLinear_comp_congr (k := k)
      (contentWhiskeredPrefixCross_equal D Sc cutoff N β i j δ _ hδ h hγ M z)
      (contentWhiskeredSuffixCross_distinct D Sc cutoff N β i hij _ h rfl M z))

theorem contentWhiskeredPathJii_eq (β : Multiset I) {i j : I} (hij : i ≠ j)
    (δ : Multiset I)
    (hδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δ)
    (hδ' : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δ)
    (hγ : δ + ([i] : Multiset I) = β + ([i,j,i] : Multiset I))
    (h : β + ([j,i,i] : Multiset I) = β + ([i,j,i] : Multiset I))
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    contentWhiskeredPathJii D Sc cutoff N β i j δ hδ hδ' hγ h M z =
      contentETriplePathJii D Sc cutoff N β i j M z :=
  contentLinear_comp_congr (k := k)
    (contentWhiskeredPrefixCross_distinct D Sc cutoff N β hij i δ _ hδ hδ' rfl h hγ M z)
    (contentLinear_comp_congr (k := k)
      (contentWhiskeredSuffixCross_equal D Sc cutoff N β j i _ h M z)
      (contentWhiskeredPrefixCross_distinct D Sc cutoff N β hij.symm i δ _ hδ' hδ h rfl hγ M z))

/-- The bookkeeping equalities identify the actual intermediate contents;
they assert no action, inverse, grading, independence or coefficient property. -/
theorem contentWhiskered_mixedBraid (β : Multiset I) {i j : I} (hij : i ≠ j)
    (δii : Multiset I)
    (hiiδ : (β + ([i] : Multiset I)) + ([i] : Multiset I) = δii)
    (hiiγ : δii + ([j] : Multiset I) = β + ([i,j,i] : Multiset I))
    (hii : β + ([i,i,j] : Multiset I) = β + ([i,j,i] : Multiset I))
    (δij : Multiset I)
    (hijδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δij)
    (hjiδ : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δij)
    (hijγ : δij + ([i] : Multiset I) = β + ([i,j,i] : Multiset I))
    (hjii : β + ([j,i,i] : Multiset I) = β + ([i,j,i] : Multiset I))
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (z : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    contentWhiskeredPathIij D (parameterTwist D Sc) cutoff N β i j δii hiiδ hiiγ hii M z -
      contentWhiskeredPathJii D (parameterTwist D Sc) cutoff N β i j δij hijδ hjiδ hijγ hjii M z =
        contentWhiskeredPolynomial D Sc cutoff N β i j M z := by
  rw [contentWhiskeredPathIij_eq D _ cutoff N β hij,
    contentWhiskeredPathJii_eq D _ cutoff N β hij,
    ← contentETripleMixedBraid, contentETriple_mixedBraid D Sc cutoff N β hij,
    contentETriplePolynomial_whiskered]
end OddMath.QuiverHecke.ELVOld
