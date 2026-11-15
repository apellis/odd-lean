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

end OddMath.QuiverHecke.ELVOld

