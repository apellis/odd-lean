import OddMath.QuiverHecke.CyclotomicAction.ELVContentBraidTransforms

/-! # The same-colour braid on direct word induction

Brundan--Ellis (1.9). Retain the normalized affine prefix and suffix as
whole module endomorphisms of direct three-letter induction. This form
is needed by the selected weight triple chart.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- The two independently induced normalized operators satisfy the
same-colour braid on every module, before weight transport. -/
theorem contentInduction_sameColour_braid (β : Multiset I) (i : I) (γ : Multiset I)
    (h : β + ([i,i,i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β) :
    (contentInductionTransform D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)).app
        (D.parity i * D.parity i) M ≫
      (contentInductionTransform D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)).app
        (D.parity i * D.parity i) M ≫
      (contentInductionTransform D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)).app
        (D.parity i * D.parity i) M =
    (contentInductionTransform D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)).app
        (D.parity i * D.parity i) M ≫
      (contentInductionTransform D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)).app
        (D.parity i * D.parity i) M ≫
      (contentInductionTransform D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)).app
        (D.parity i * D.parity i) M := by
  apply BalancedInduction.supernatural_ext_total
  intro z
  rw [Superfunctor.comp_total, Superfunctor.comp_total, Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [contentInductionTransform_total]
  change (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)) M z).comp ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)) M z).comp (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)) M z)) =
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)) M z).comp ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)) M z).comp (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)) M z))
  apply BalancedInduction.hom_ext
  intro v g b
  rw [contentTripleTransform_tensor D Sc cutoff N h h h h
    (contentNormalizedRight_mem D Sc i i i) (contentNormalizedLeft_mem D Sc i i i)
    (contentNormalizedRight_mem D Sc i i i) M z v g b]
  rw [contentTripleTransform_tensor D Sc cutoff N h h h h
    (contentNormalizedLeft_mem D Sc i i i) (contentNormalizedRight_mem D Sc i i i)
    (contentNormalizedLeft_mem D Sc i i i) M z v g b]
  rw [contentNormalized_braid D Sc i i i (by simp)]

end OddMath.QuiverHecke.ELVOld
