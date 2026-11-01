/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentDotTransforms
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBraidTransforms
import OddMath.QuiverHecke.CyclotomicAction.ELVContentWhiskeredMixedBraid

/-! # The corrected mixed braid of independent supernatural families

The correction is the ordered polynomial in the three independently induced
dot families. Its scalar parameters are the original parameters, while the
module category uses their parameter twist.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- The two levels of total evaluation preserve all ordered polynomial operations. -/
def doubleSupernaturalTotalEndAlgHom
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (F : Superfunctor k C (Superfunctor k B (SVec.{u} k))) (M : C) (z : B) :
    End F →ₐ[k] End ((F.obj M).obj z) :=
  (supernaturalTotalEndAlgHom (F.obj M) z).comp (supernaturalTotalEndAlgHom F M)

theorem contentTripleFirstDotTransform_evaluation
    (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentTripleFirstDotTransform D Sc cutoff N β i j l γ h).total M).total z =
      contentWhiskeredFirstDot D Sc cutoff N β i j l γ h M z := by
  rw [contentTripleFirstDotTransform_total]
  rfl

theorem contentTripleMiddleDotTransform_evaluation
    (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentTripleMiddleDotTransform D Sc cutoff N β i j l γ h).total M).total z =
      contentWhiskeredMiddleDot D Sc cutoff N β i j l γ h M z := by
  rw [contentTripleMiddleDotTransform_total]
  rfl

theorem contentTripleLastDotTransform_evaluation
    (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentTripleLastDotTransform D Sc cutoff N β i j l γ h).total M).total z =
      contentWhiskeredLastDot D Sc cutoff N β i j l γ h M z := by
  rw [contentTripleLastDotTransform_total]
  rfl

def contentTripleDotSumTransform (β : Multiset I) (i j : I) (r s : ℕ) (d : k) :
    End (contentETripleSuperfunctor D Sc cutoff N β i j i
      (β + ([i,j,i] : Multiset I)) rfl) :=
  let A : End (contentETripleSuperfunctor D Sc cutoff N β i j i _ rfl) :=
    contentTripleFirstDotTransform D Sc cutoff N β i j i _ rfl
  let B : End (contentETripleSuperfunctor D Sc cutoff N β i j i _ rfl) :=
    contentTripleMiddleDotTransform D Sc cutoff N β i j i _ rfl
  let C : End (contentETripleSuperfunctor D Sc cutoff N β i j i _ rfl) :=
    contentTripleLastDotTransform D Sc cutoff N β i j i _ rfl
  ∑ q ∈ Finset.range r,
    (SKM.zsign k (D.parity i * (D.parity j + q)) * d) •
      (C ^ (r - 1 - q) * B ^ s * A ^ q)

theorem contentTripleDotSumTransform_evaluation (β : Multiset I) (i j : I)
    (r s : ℕ) (d : k) (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    ((contentTripleDotSumTransform D Sc cutoff N β i j r s d).total M).total z =
      contentWhiskeredDotSum D Sc cutoff N β i j r s d M z := by
  let ev := doubleSupernaturalTotalEndAlgHom
    (contentETripleSuperfunctor D Sc cutoff N β i j i _ rfl) M z
  change ev (contentTripleDotSumTransform D Sc cutoff N β i j r s d) = _
  simp only [contentTripleDotSumTransform, map_sum, map_smul, map_mul, map_pow]
  change (∑ q ∈ Finset.range r,
    (SKM.zsign k (D.parity i * (D.parity j + q)) * d) •
      ((((contentTripleLastDotTransform D Sc cutoff N β i j i _ rfl).total M).total z) ^
        (r - 1 - q) *
       (((contentTripleMiddleDotTransform D Sc cutoff N β i j i _ rfl).total M).total z) ^ s *
       (((contentTripleFirstDotTransform D Sc cutoff N β i j i _ rfl).total M).total z) ^ q)) = _
  simp only [contentTripleFirstDotTransform_evaluation, contentTripleMiddleDotTransform_evaluation,
    contentTripleLastDotTransform_evaluation, contentWhiskeredDotSum]

def contentTriplePolynomialTransform (β : Multiset I) (i j : I) :
    End (contentETripleSuperfunctor D (parameterTwist D Sc) cutoff N β i j i
      (β + ([i,j,i] : Multiset I)) rfl) :=
  contentTripleDotSumTransform D (parameterTwist D Sc) cutoff N β i j
      (D.dn i j) 0 (Sc.t i j) +
    ∑ r ∈ Finset.Ioo 0 (D.dn i j), ∑ s ∈ Finset.Ioo 0 (D.dn j i),
      contentTripleDotSumTransform D (parameterTwist D Sc) cutoff N β i j r s (Sc.s i j r s)

theorem contentTriplePolynomialTransform_evaluation (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (z : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    ((contentTriplePolynomialTransform D Sc cutoff N β i j).total M).total z =
      contentWhiskeredPolynomial D Sc cutoff N β i j M z := by
  let ev := doubleSupernaturalTotalEndAlgHom
    (contentETripleSuperfunctor D (parameterTwist D Sc) cutoff N β i j i _ rfl) M z
  change ev (contentTriplePolynomialTransform D Sc cutoff N β i j) = _
  simp only [contentTriplePolynomialTransform, map_add, map_sum]
  change ((contentTripleDotSumTransform D (parameterTwist D Sc) cutoff N β i j
      (D.dn i j) 0 (Sc.t i j)).total M).total z +
    (∑ r ∈ Finset.Ioo 0 (D.dn i j), ∑ s ∈ Finset.Ioo 0 (D.dn j i),
      ((contentTripleDotSumTransform D (parameterTwist D Sc) cutoff N β i j r s
        (Sc.s i j r s)).total M).total z) = _
  simp only [contentTripleDotSumTransform_evaluation, contentWhiskeredPolynomial]

def contentMixedPathIijTransform (β : Multiset I) (i j : I) (δii : Multiset I)
    (hiiδ : (β + ([i] : Multiset I)) + ([i] : Multiset I) = δii)
    (hiiγ : δii + ([j] : Multiset I) = β + ([i,j,i] : Multiset I)) :
    End (contentETripleSuperfunctor D Sc cutoff N β i j i _ rfl) :=
  contentBraidRightTransform D Sc cutoff N β i j i _ rfl
    (content_triple_iij β i j) (content_triple_iij β i j) rfl δii hiiδ hiiδ hiiγ

def contentMixedPathJiiTransform (β : Multiset I) (i j : I) (δij : Multiset I)
    (hijδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δij)
    (hjiδ : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δij)
    (hijγ : δij + ([i] : Multiset I) = β + ([i,j,i] : Multiset I)) :
    End (contentETripleSuperfunctor D Sc cutoff N β i j i _ rfl) :=
  contentBraidLeftTransform D Sc cutoff N β i j i _ rfl
    (content_triple_jii β i j) (content_triple_jii β i j) rfl
    δij hijδ hjiδ hijγ δij hjiδ hijδ hijγ

theorem contentMixedPathIijTransform_evaluation (β : Multiset I) (i j : I) (δii : Multiset I)
    (hiiδ : (β + ([i] : Multiset I)) + ([i] : Multiset I) = δii)
    (hiiγ : δii + ([j] : Multiset I) = β + ([i,j,i] : Multiset I))
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    ((contentMixedPathIijTransform D Sc cutoff N β i j δii hiiδ hiiγ).total M).total z =
      contentWhiskeredPathIij D Sc cutoff N β i j δii hiiδ hiiγ
        (content_triple_iij β i j) M z :=
  contentBraidRightTransform_evaluation D Sc cutoff N β i j i _ rfl
    (content_triple_iij β i j) (content_triple_iij β i j) rfl δii hiiδ hiiδ hiiγ M z

theorem contentMixedPathJiiTransform_evaluation (β : Multiset I) (i j : I) (δij : Multiset I)
    (hijδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δij)
    (hjiδ : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δij)
    (hijγ : δij + ([i] : Multiset I) = β + ([i,j,i] : Multiset I))
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    ((contentMixedPathJiiTransform D Sc cutoff N β i j δij hijδ hjiδ hijγ).total M).total z =
      contentWhiskeredPathJii D Sc cutoff N β i j δij hijδ hjiδ hijγ
        (content_triple_jii β i j) M z :=
  contentBraidLeftTransform_evaluation D Sc cutoff N β i j i _ rfl
    (content_triple_jii β i j) (content_triple_jii β i j) rfl
    δij hijδ hjiδ hijγ δij hjiδ hijδ hijγ M z

/-- The full corrected braid of independently induced supernatural families. -/
theorem contentMixedBraidTransform (β : Multiset I) {i j : I} (hij : i ≠ j)
    (δii : Multiset I)
    (hiiδ : (β + ([i] : Multiset I)) + ([i] : Multiset I) = δii)
    (hiiγ : δii + ([j] : Multiset I) = β + ([i,j,i] : Multiset I))
    (δij : Multiset I)
    (hijδ : (β + ([i] : Multiset I)) + ([j] : Multiset I) = δij)
    (hjiδ : (β + ([j] : Multiset I)) + ([i] : Multiset I) = δij)
    (hijγ : δij + ([i] : Multiset I) = β + ([i,j,i] : Multiset I)) :
    contentMixedPathIijTransform D (parameterTwist D Sc) cutoff N β i j δii hiiδ hiiγ -
      contentMixedPathJiiTransform D (parameterTwist D Sc) cutoff N β i j δij hijδ hjiδ hijγ =
        contentTriplePolynomialTransform D Sc cutoff N β i j := by
  apply BalancedInduction.supernatural_ext_total
  intro M
  apply BalancedInduction.supernatural_ext_total
  intro z
  let ev := doubleSupernaturalTotalEndAlgHom
    (contentETripleSuperfunctor D (parameterTwist D Sc) cutoff N β i j i _ rfl) M z
  change ev (contentMixedPathIijTransform D (parameterTwist D Sc) cutoff N β i j δii hiiδ hiiγ -
      contentMixedPathJiiTransform D (parameterTwist D Sc) cutoff N β i j δij hijδ hjiδ hijγ) =
    ev (contentTriplePolynomialTransform D Sc cutoff N β i j)
  rw [map_sub]
  change ((contentMixedPathIijTransform D (parameterTwist D Sc) cutoff N β i j δii hiiδ hiiγ).total M).total z -
      ((contentMixedPathJiiTransform D (parameterTwist D Sc) cutoff N β i j δij hijδ hjiδ hijγ).total M).total z =
        ((contentTriplePolynomialTransform D Sc cutoff N β i j).total M).total z
  rw [contentMixedPathIijTransform_evaluation, contentMixedPathJiiTransform_evaluation,
    contentTriplePolynomialTransform_evaluation]
  exact contentWhiskered_mixedBraid D Sc cutoff N β hij δii hiiδ hiiγ
    (content_triple_iij β i j) δij hijδ hjiδ hijγ (content_triple_jii β i j) M z

end OddMath.QuiverHecke.ELVOld
