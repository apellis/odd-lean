/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockExtension
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedInductionNaturality

/-! # Chosen append comparisons for truncated content blocks

For the canonical multiset-content realization of Brundan–Ellis (1.12),
induction and restriction are compared with global truncated append
using the literal inclusion square, its even unit, and its supported
counit. Arbitrary common upper contents are retained explicitly.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- The append/inclusion square is literal on objects and whole quotient arrows. -/
theorem contentAppendTo_inclusion (β : Multiset I) (σ : List I) (γ : Multiset I)
    (h : β + (σ : Multiset I) = γ) :
    contentAppendTo D Sc cutoff N β σ γ h ⋙ contentInclusion D Sc cutoff N γ =
      contentInclusion D Sc cutoff N β ⋙ truncatedAppend D Sc cutoff N σ := rfl

/-- The chosen comparison of append induction followed by full-content extension. -/
def contentAppendToExtensionIso (β : Multiset I) (σ : List I) (γ : Multiset I)
    (h : β + (σ : Multiset I) = γ) :
    BalancedInduction.induction (k := k) (contentAppendTo D Sc cutoff N β σ γ h) ⋙
        BalancedInduction.induction (contentInclusion D Sc cutoff N γ) ≅
      BalancedInduction.induction (contentInclusion D Sc cutoff N β) ⋙
        BalancedInduction.induction (truncatedAppend D Sc cutoff N σ) :=
  BalancedInduction.inductionComp (contentAppendTo D Sc cutoff N β σ γ h)
      (contentInclusion D Sc cutoff N γ) ≪≫
    BalancedInduction.inductionFunctorIsoOfEq _ _ (contentAppendTo_inclusion D Sc cutoff N β σ γ h) ≪≫
    (BalancedInduction.inductionComp (contentInclusion D Sc cutoff N β)
      (truncatedAppend D Sc cutoff N σ)).symm

/-- Restricting global append of the canonical extension recovers chosen content induction. -/
def contentAppendToRestrictionIso (β : Multiset I) (σ : List I) (γ : Multiset I)
    (h : β + (σ : Multiset I) = γ) (M : ContentModules D Sc cutoff N β) :
    BalancedInduction.induced (contentAppendTo D Sc cutoff N β σ γ h) M ≅
      (BalancedInduction.restriction (contentInclusion D Sc cutoff N γ)).obj
        (BalancedInduction.induced (truncatedAppend D Sc cutoff N σ)
          (BalancedInduction.induced (contentInclusion D Sc cutoff N β) M)) :=
  contentExtensionUnitIso D Sc cutoff N γ
      (BalancedInduction.induced (contentAppendTo D Sc cutoff N β σ γ h) M) ≪≫
    (BalancedInduction.restriction (contentInclusion D Sc cutoff N γ)).mapIso
      ((contentAppendToExtensionIso D Sc cutoff N β σ γ h).app M)

/-- Single-colour restriction subtracts its colour from the precise support. -/
theorem contentAppendRestriction_supported (β : Multiset I) (i : I) (γ : Multiset I)
    (h : β + ([i] : Multiset I) = γ)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (hM : ContentSupported D Sc cutoff N γ M) :
    ContentSupported D Sc cutoff N β
      ((BalancedInduction.restriction (truncatedAppend D Sc cutoff N [i])).obj M) := by
  intro w hw
  apply hM ((truncatedAppend D Sc cutoff N [i]).obj w)
  intro he
  apply hw
  change (w.word : Multiset I) + ([i] : Multiset I) = γ at he
  exact add_right_cancel (he.trans h.symm)

/-- Both restrictions around the selected inclusion square agree literally. -/
def contentAppendToRestrictionSquare (β : Multiset I) (σ : List I) (γ : Multiset I)
    (h : β + (σ : Multiset I) = γ)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (BalancedInduction.restriction (contentAppendTo D Sc cutoff N β σ γ h)).obj
        ((BalancedInduction.restriction (contentInclusion D Sc cutoff N γ)).obj M) ≅
      (BalancedInduction.restriction (contentInclusion D Sc cutoff N β)).obj
        ((BalancedInduction.restriction (truncatedAppend D Sc cutoff N σ)).obj M) := Iso.refl _

/-- Extending content restriction is global restriction of the canonical extension. -/
def contentAppendToRestrictionExtensionIso (β : Multiset I) (i : I) (γ : Multiset I)
    (h : β + ([i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N γ) :
    BalancedInduction.induced (contentInclusion D Sc cutoff N β)
        ((BalancedInduction.restriction (contentAppendTo D Sc cutoff N β [i] γ h)).obj M) ≅
      (BalancedInduction.restriction (truncatedAppend D Sc cutoff N [i])).obj
        (BalancedInduction.induced (contentInclusion D Sc cutoff N γ) M) :=
  (BalancedInduction.induction (contentInclusion D Sc cutoff N β)).mapIso
    ((BalancedInduction.restriction (contentAppendTo D Sc cutoff N β [i] γ h)).mapIso
      (contentExtensionUnitIso D Sc cutoff N γ M) ≪≫
      contentAppendToRestrictionSquare D Sc cutoff N β [i] γ h
        (BalancedInduction.induced (contentInclusion D Sc cutoff N γ) M)) ≪≫
    contentSupportedCounitIso D Sc cutoff N β _
      (contentAppendRestriction_supported D Sc cutoff N β i γ h _
        (contentExtension_supported D Sc cutoff N γ M))

end OddMath.QuiverHecke.ELVOld
