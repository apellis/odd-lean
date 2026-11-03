/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppend
import OddMath.QuiverHecke.CyclotomicAction.ELVContentRestrictionTensor

/-! # Restriction chart tensors on canonical truncated content

The selected full-inclusion unit/counit comparison for Brundan–Ellis
(1.12) sends the entire quotient-arrow generator `[g ⊗ b]` to
`[append(g) ⊗ b]`. No parity restriction on either factor is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- The comparison is the induction of the actual inclusion unit followed by
its actual inclusion counit; the append/inclusion restriction square is strict. -/
theorem contentAppendToRestrictionExtensionIso_hom (β : Multiset I) (i : I) (γ : Multiset I)
    (h : β + ([i] : Multiset I) = γ)
    (P : Superfunctor k (ContentCategory D Sc cutoff N γ) (SVec k)) :
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ h P).hom =
      (BalancedInduction.induction (contentInclusion D Sc cutoff N β)).map
        ((BalancedInduction.restriction (contentAppendTo D Sc cutoff N β [i] γ h)).map
          ((BalancedInduction.adjunctionUnit
            (contentInclusion D Sc cutoff N γ)).app P)) ≫
      (BalancedInduction.adjunctionCounit (contentInclusion D Sc cutoff N β)).app
        ((BalancedInduction.restriction (truncatedAppend D Sc cutoff N [i])).obj
          (BalancedInduction.induced (contentInclusion D Sc cutoff N γ) P)) := by
  simp only [contentAppendToRestrictionExtensionIso, Iso.trans_hom, Functor.mapIso_hom,
    contentAppendToRestrictionSquare, Iso.refl_hom, Category.comp_id,
    contentExtensionUnitIso, BalancedInduction.fullyFaithfulUnitIso_hom,
    contentSupportedCounitIso_hom]

/-- The prescribed source-arrow generator is unchanged and its quotient arrow is appended. -/
theorem contentAppendToRestrictionExtensionIso_tensor (β : Multiset I) (i : I) (γ : Multiset I)
    (h : β + ([i] : Multiset I) = γ)
    (P : Superfunctor k (ContentCategory D Sc cutoff N γ) (SVec k))
    (w : TruncatedCategory D Sc cutoff N) (s : ContentCategory D Sc cutoff N β)
    (g : (contentInclusion D Sc cutoff N β).obj s ⟶ w)
    (b : P.obj ((contentAppendTo D Sc cutoff N β [i] γ h).obj s)) :
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ h P).hom.total w
      (BalancedInduction.tensor (contentInclusion D Sc cutoff N β)
        ((BalancedInduction.restriction (contentAppendTo D Sc cutoff N β [i] γ h)).obj P).toFunctor s g b) =
      BalancedInduction.tensor (contentInclusion D Sc cutoff N γ) P.toFunctor
        ((contentAppendTo D Sc cutoff N β [i] γ h).obj s) ((truncatedAppend D Sc cutoff N [i]).map g) b := by
  rw [contentAppendToRestrictionExtensionIso_hom, Superfunctor.comp_total]
  change ((BalancedInduction.adjunctionCounit (contentInclusion D Sc cutoff N β)).app
      ((BalancedInduction.restriction (truncatedAppend D Sc cutoff N [i])).obj
        (BalancedInduction.induced (contentInclusion D Sc cutoff N γ) P))).total w
      ((BalancedInduction.moduleMap (contentInclusion D Sc cutoff N β)
        ((BalancedInduction.restriction (contentAppendTo D Sc cutoff N β [i] γ h)).map
          ((BalancedInduction.adjunctionUnit
            (contentInclusion D Sc cutoff N γ)).app P))).total w
        (BalancedInduction.tensor (contentInclusion D Sc cutoff N β)
          ((BalancedInduction.restriction (contentAppendTo D Sc cutoff N β [i] γ h)).obj P).toFunctor
            s g b)) = _
  rw [BalancedInduction.counit_total_apply]
  have hm := BalancedInduction.moduleMap_total_tensor
    (contentInclusion D Sc cutoff N β)
    ((BalancedInduction.restriction (contentAppendTo D Sc cutoff N β [i] γ h)).map
      ((BalancedInduction.adjunctionUnit (contentInclusion D Sc cutoff N γ)).app P))
    w s g b
  refine (congrArg (BalancedInduction.counit (contentInclusion D Sc cutoff N β)
    ((BalancedInduction.restriction (truncatedAppend D Sc cutoff N [i])).obj
      (BalancedInduction.induced (contentInclusion D Sc cutoff N γ) P)).toFunctor w) hm).trans ?_
  change BalancedInduction.counit (contentInclusion D Sc cutoff N β)
      ((BalancedInduction.restriction (truncatedAppend D Sc cutoff N [i])).obj
        (BalancedInduction.induced (contentInclusion D Sc cutoff N γ) P)).toFunctor w
      (BalancedInduction.tensor (contentInclusion D Sc cutoff N β) _ s g
        (BalancedInduction.unit (contentInclusion D Sc cutoff N γ) P.toFunctor
          ((contentAppendTo D Sc cutoff N β [i] γ h).obj s) b) +
        BalancedInduction.tensor (contentInclusion D Sc cutoff N β) _ s (twist k 1 g) 0) = _
  rw [BalancedInduction.tensor_zero_right, add_zero, BalancedInduction.counit_tensor]
  change BalancedInduction.postcompose (contentInclusion D Sc cutoff N γ) P.toFunctor
      ((truncatedAppend D Sc cutoff N [i]).map g)
      (BalancedInduction.unit (contentInclusion D Sc cutoff N γ) P.toFunctor
        ((contentAppendTo D Sc cutoff N β [i] γ h).obj s) b) = _
  rw [BalancedInduction.unit_apply, BalancedInduction.postcompose_tensor, Category.id_comp]

end OddMath.QuiverHecke.ELVOld
