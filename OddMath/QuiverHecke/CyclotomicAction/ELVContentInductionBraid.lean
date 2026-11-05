import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleCrossingNormalization
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSuffixCrossingTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVContentUncorrectedBraid

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
private theorem moduleBraid_of_total
    {k : Type u} [CommRing k]
    {C : Type*} [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (L R : End M)
    (a b : ∀ w, M.obj w →ₗ[k] M.obj w)
    (hL : ∀ w, L.total w = a w) (hR : ∀ w, R.total w = b w)
    (hb : ∀ w, (b w).comp ((a w).comp (b w)) = (a w).comp ((b w).comp (a w))) :
    R ≫ L ≫ R = L ≫ R ≫ L := by
  apply BalancedInduction.supernatural_ext_total
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total, Superfunctor.comp_total, Superfunctor.comp_total]
  change (R.total w).comp ((L.total w).comp (R.total w)) =
    (L.total w).comp ((R.total w).comp (L.total w))
  rw [hL, hR, hb]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Pure coend form of the normalized same-colour braid, with all word endpoints pinned. -/
theorem contentInduction_sameColour_linear_braid
    (β : Multiset I) (i : I) (γ : Multiset I)
    (h : β + ([i,i,i] : Multiset I) = γ) (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N γ) :
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)) M z).comp ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)) M z).comp (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)) M z)) =
      (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)) M z).comp ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)) M z).comp (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)) M z)) := by
  apply BalancedInduction.hom_ext
  intro v g b
  rw [contentTripleTransform_tensor D Sc cutoff N
    (σ := [i,i,i]) (τ := [i,i,i]) (υ := [i,i,i]) (ω := [i,i,i]) h h h h
    (contentNormalizedRight_mem D Sc i i i) (contentNormalizedLeft_mem D Sc i i i)
    (contentNormalizedRight_mem D Sc i i i) M z v g b]
  rw [contentTripleTransform_tensor D Sc cutoff N
    (σ := [i,i,i]) (τ := [i,i,i]) (υ := [i,i,i]) (ω := [i,i,i]) h h h h
    (contentNormalizedLeft_mem D Sc i i i) (contentNormalizedRight_mem D Sc i i i)
    (contentNormalizedLeft_mem D Sc i i i) M z v g b]
  rw [contentNormalized_braid D Sc i i i (by simp)]

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
  apply moduleBraid_of_total
    ((contentInductionTo D Sc cutoff N β [i,i,i] γ h).obj M)
    ((contentInductionTransform D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)).app
      (D.parity i * D.parity i) M)
    ((contentInductionTransform D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)).app
      (D.parity i * D.parity i) M)
    (fun z => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i)) M z)
    (fun z => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i)) M z)
  · intro z
    exact contentInductionTransform_total D Sc cutoff N h h (contentNormalizedLeft_mem D Sc i i i) M z
  · intro z
    exact contentInductionTransform_total D Sc cutoff N h h (contentNormalizedRight_mem D Sc i i i) M z
  · intro z
    exact contentInduction_sameColour_linear_braid D Sc cutoff N β i γ h M z

end OddMath.QuiverHecke.ELVOld
