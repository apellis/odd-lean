/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Whiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMixedPolynomial

/-! # Canonical triple-E transport of the corrected mixed braid

Advances `DeformedActionAssembly.md` §6 with an even all-module comparison
from three successive single-letter E functors to block induction. Intermediate
and final content equalities are explicit. The same recursively constructed
comparison is used at every word, so both three-crossing paths transport
coherently; the checked source maps and both equal-crossing minus signs are
retained. The polynomial has exactly original Sc and three ordered dot powers.
The linear arrows are evaluated genuine supernatural transformations, and the
residual twist on the entire coefficient/diagram kernel is stated explicitly.

This proves path compatibility for these canonical transported source maps.
It does not yet identify them with independently whiskered pair crossings/dots
or prove equality of the two possible recursive associativity comparisons.
No weight assembly, local inversions or nondegeneracy is claimed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem evenComparison_trans
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G H : C ⥤ B} (e : F ≅ G) (f : G ≅ H) (M : C)
    (he : EvenComparisonAt (k := k) e M) (hf : EvenComparisonAt (k := k) f M) :
    EvenComparisonAt (k := k) (e ≪≫ f) M :=
  ⟨comp_mem he.1 hf.1, comp_mem hf.2 he.2⟩

private theorem evenComparison_whisker
    {C B E : Type*} [Category* C] [Category* B] [Category* E]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : C ⥤ B} (e : F ≅ G) (K : B ⥤ E)
    [K.Additive] [K.Linear k] [IsSuperfunctor k K] (M : C)
    (he : EvenComparisonAt (k := k) e M) :
    EvenComparisonAt (k := k) (Functor.isoWhiskerRight e K) M :=
  ⟨Supercategory.map_mem K he.1, Supercategory.map_mem K he.2⟩

theorem contentAppend_compTo_eq (β : Multiset I) (σ : List I) (δ : Multiset I)
    (hδ : β + (σ : Multiset I) = δ) (τ : List I) (γ : Multiset I)
    (hγ : δ + (τ : Multiset I) = γ)
    (h : β + ((σ ++ τ : List I) : Multiset I) = γ) :
    contentAppendTo D Sc cutoff N β σ δ hδ ⋙ contentAppendTo D Sc cutoff N δ τ γ hγ =
      contentAppendTo D Sc cutoff N β (σ ++ τ) γ h := by
  subst δ
  exact contentAppend_comp_eq D Sc cutoff N β σ τ γ hγ h

/-- The intermediate content equality is explicit as well. -/
def contentInductionCompTo (β : Multiset I) (σ : List I) (δ : Multiset I)
    (hδ : β + (σ : Multiset I) = δ) (τ : List I) (γ : Multiset I)
    (hγ : δ + (τ : Multiset I) = γ) (h : β + ((σ ++ τ : List I) : Multiset I) = γ) :
    contentInductionTo D Sc cutoff N β σ δ hδ ⋙ contentInductionTo D Sc cutoff N δ τ γ hγ ≅
      contentInductionTo D Sc cutoff N β (σ ++ τ) γ h := by
  subst δ
  exact contentInductionComp D Sc cutoff N β σ τ γ hγ h

theorem contentInductionCompTo_mem (β : Multiset I) (σ : List I) (δ : Multiset I)
    (hδ : β + (σ : Multiset I) = δ) (τ : List I) (γ : Multiset I)
    (hγ : δ + (τ : Multiset I) = γ) (h : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) :
    EvenComparisonAt (k := k) (contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h) M := by
  subst δ
  exact contentInductionComp_mem D Sc cutoff N β σ τ γ hγ h M

/-- Three actual single-letter E functors; only the final content is recast. -/
abbrev contentETripleTo (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) :=
  (contentE D Sc cutoff N β i ⋙ contentE D Sc cutoff N (β + ([i] : Multiset I)) j) ⋙
    contentInductionTo D Sc cutoff N ((β + ([i] : Multiset I)) + ([j] : Multiset I)) [l] γ
      (by rw [add_assoc, add_assoc]; exact h)

def contentETripleComparison (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) :
    contentETripleTo D Sc cutoff N β i j l γ h ≅ contentInductionTo D Sc cutoff N β [i,j,l] γ h :=
  Functor.isoWhiskerRight (contentEPairComparison D Sc cutoff N β i j)
    (contentInductionTo D Sc cutoff N ((β + ([i] : Multiset I)) + ([j] : Multiset I)) [l] γ
      (by rw [add_assoc, add_assoc]; exact h)) ≪≫
  contentInductionCompTo D Sc cutoff N β [i,j]
    ((β + ([i] : Multiset I)) + ([j] : Multiset I)) (by rw [add_assoc]; rfl)
    [l] γ _ h

theorem contentETripleComparison_mem (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β) :
    EvenComparisonAt (k := k) (contentETripleComparison D Sc cutoff N β i j l γ h) M :=
  evenComparison_trans _ _ M
    (evenComparison_whisker (contentEPairComparison D Sc cutoff N β i j)
      (contentInductionTo D Sc cutoff N ((β + ([i] : Multiset I)) + ([j] : Multiset I)) [l] γ
        (by rw [add_assoc, add_assoc]; exact h)) M
      (contentInductionComp_mem D Sc cutoff N β [i] [j] _ rfl _ M))
    (contentInductionCompTo_mem D Sc cutoff N β [i,j]
      ((β + ([i] : Multiset I)) + ([j] : Multiset I)) (by rw [add_assoc]; rfl) [l] γ _ h M)

/-- The carrier of the actual evaluated triple functor, with its inherited
SVec module instances shared by the independent natural transformations. -/
abbrev ContentETripleSpace (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) : Type u :=
  (((contentETripleTo D Sc cutoff N β i j l γ h).obj M).obj w).carrier

def contentETripleEquiv (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) :
    ((contentETripleTo D Sc cutoff N β i j l γ h).obj M).obj w ≃ₗ[k]
      (((contentInductionTo D Sc cutoff N β [i,j,l] γ h).obj M).obj w).carrier :=
  moduleIsoLinearEquiv ((contentETripleComparison D Sc cutoff N β i j l γ h).app M) w

/-- The source-positioned map on three successive E functors. -/
def contentETripleMap {β γ : Multiset I} {i j l a b c : I}
    (hσ : β + ([i,j,l] : Multiset I) = γ)
    (hτ : β + ([a,b,c] : Multiset I) = γ) {p : ZMod 2}
    {f : (pres D Sc).obj (ob D [i,j,l]) ⟶ (pres D Sc).obj (ob D [a,b,c])}
    (hf : f ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ) :
    ((contentETripleTo D Sc cutoff N β a b c γ hτ).obj M).obj w ⟶
      ((contentETripleTo D Sc cutoff N β i j l γ hσ).obj M).obj w :=
  (contentETripleEquiv D Sc cutoff N β i j l γ hσ M w).symm.toLinearMap.comp
    ((BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N hσ hτ hf) M w).comp
      (contentETripleEquiv D Sc cutoff N β a b c γ hτ M w).toLinearMap)

def contentETriplePathIij (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M w) :=
  let A := contentETripleMap D Sc cutoff N rfl (content_triple_iij β i j)
    (contentTripleRight_parity D Sc i j i) M w
  let B := contentETripleMap D Sc cutoff N (content_triple_iij β i j) (content_triple_iij β i j)
    (contentTripleLeft_parity D Sc i i j) M w
  let C := contentETripleMap D Sc cutoff N (content_triple_iij β i j) rfl
    (contentTripleRight_parity D Sc i i j) M w
  A.comp ((-B).comp C)

def contentETriplePathJii (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M w) :=
  let E := contentETripleMap D Sc cutoff N rfl (content_triple_jii β i j)
    (contentTripleLeft_parity D Sc i j i) M w
  let F := contentETripleMap D Sc cutoff N (content_triple_jii β i j) (content_triple_jii β i j)
    (contentTripleRight_parity D Sc j i i) M w
  let G := contentETripleMap D Sc cutoff N (content_triple_jii β i j) rfl
    (contentTripleLeft_parity D Sc j i i) M w
  E.comp ((-F).comp G)

def contentETripleMixedBraid (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M w) :=
  contentETriplePathIij D Sc cutoff N β i j M w - contentETriplePathJii D Sc cutoff N β i j M w

def contentBlockPathIij (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (BalancedInduction.Obj
      (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl) M.toFunctor w) :=
  let A := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N rfl (content_triple_iij β i j)
      (contentTripleRight_parity D Sc i j i)) M w
  let B := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_iij β i j) (content_triple_iij β i j)
      (contentTripleLeft_parity D Sc i i j)) M w
  let C := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_iij β i j) rfl
      (contentTripleRight_parity D Sc i i j)) M w
  A.comp ((-B).comp C)

def contentBlockPathJii (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (BalancedInduction.Obj
      (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl) M.toFunctor w) :=
  let A := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N rfl (content_triple_jii β i j)
      (contentTripleLeft_parity D Sc i j i)) M w
  let B := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_jii β i j) (content_triple_jii β i j)
      (contentTripleRight_parity D Sc j i i)) M w
  let C := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_jii β i j) rfl
      (contentTripleLeft_parity D Sc j i i)) M w
  A.comp ((-B).comp C)

/-- All three positioned dots use the same canonical even comparison. -/
def contentETripleDot (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) (a : Fin 3) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M w) :=
  (contentETripleEquiv D Sc cutoff N β i j i _ rfl M w).symm.conjAlgEquiv k
    (if a = 0 then contentInductionEndLinear D Sc cutoff N (firstDot_parity D Sc i [j,i]) M w
     else if a = 1 then contentInductionEndLinear D Sc cutoff N (contentTripleDot_one_parity D Sc i j) M w
     else contentInductionEndLinear D Sc cutoff N (contentTripleDot_two_parity D Sc i j) M w)

def contentETripleDotSum (β : Multiset I) (i j : I) (r s : ℕ) (d : k)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D Sc cutoff N β i j i _ rfl M w) :=
  let A := contentETripleDot D Sc cutoff N β i j M w 0
  let B := contentETripleDot D Sc cutoff N β i j M w 1
  let C := contentETripleDot D Sc cutoff N β i j M w 2
  ∑ l ∈ Finset.range r, (SKM.zsign k (D.parity i*(D.parity j+l))*d) • (C^(r-1-l)*B^s*A^l)

/-- Ordered three-dot correction with the original Sc, including the leading t term. -/
def contentETriplePolynomial (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    Module.End k (ContentETripleSpace D (parameterTwist D Sc) cutoff N β i j i _ rfl M w) :=
  contentETripleDotSum D (parameterTwist D Sc) cutoff N β i j (D.dn i j) 0 (Sc.t i j : k) M w +
    ∑ r ∈ Finset.Ioo 0 (D.dn i j), ∑ s ∈ Finset.Ioo 0 (D.dn j i),
      contentETripleDotSum D (parameterTwist D Sc) cutoff N β i j r s (Sc.s i j r s) M w

end OddMath.QuiverHecke.ELVOld

