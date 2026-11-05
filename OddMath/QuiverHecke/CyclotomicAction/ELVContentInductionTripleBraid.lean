import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleCrossingNormalization
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSuffixCrossingTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVContentUncorrectedBraid

/-! # The multicolour braid on direct word induction

Brundan--Ellis (1.9), outside the repeated-outer correction case. The
normalized direct affine prefix and suffix satisfy the whole module-map
braid between the six word inductions. This form is consumed by the
independently selected weight triple charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem moduleThree_eq_of_totals
    {k : Type u} [CommRing k]
    {C : Type*} [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    (M₀ M₁ M₂ M₃ M₄ M₅ : Superfunctor k C (SVec k))
    (a₀ : M₀ ⟶ M₁) (a₁ : M₁ ⟶ M₂) (a₂ : M₂ ⟶ M₃)
    (b₀ : M₀ ⟶ M₄) (b₁ : M₄ ⟶ M₅) (b₂ : M₅ ⟶ M₃)
    (f₀ : ∀ w, M₀.obj w →ₗ[k] M₁.obj w) (f₁ : ∀ w, M₁.obj w →ₗ[k] M₂.obj w)
    (f₂ : ∀ w, M₂.obj w →ₗ[k] M₃.obj w) (g₀ : ∀ w, M₀.obj w →ₗ[k] M₄.obj w)
    (g₁ : ∀ w, M₄.obj w →ₗ[k] M₅.obj w) (g₂ : ∀ w, M₅.obj w →ₗ[k] M₃.obj w)
    (ha₀ : ∀ w, a₀.total w = f₀ w) (ha₁ : ∀ w, a₁.total w = f₁ w) (ha₂ : ∀ w, a₂.total w = f₂ w)
    (hb₀ : ∀ w, b₀.total w = g₀ w) (hb₁ : ∀ w, b₁.total w = g₁ w) (hb₂ : ∀ w, b₂.total w = g₂ w)
    (hh : ∀ w, (f₂ w).comp ((f₁ w).comp (f₀ w)) = (g₂ w).comp ((g₁ w).comp (g₀ w))) :
    a₀ ≫ a₁ ≫ a₂ = b₀ ≫ b₁ ≫ b₂ := by
  apply BalancedInduction.supernatural_ext_total
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total, Superfunctor.comp_total, Superfunctor.comp_total]
  change (a₂.total w).comp ((a₁.total w).comp (a₀.total w)) =
    (b₂.total w).comp ((b₁.total w).comp (b₀.total w))
  rw [ha₀, ha₁, ha₂, hb₀, hb₁, hb₂, hh]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
private theorem inductionLinear_braid (β : Multiset I) (i j l : I)
    (hb : ¬ (i = l ∧ i ≠ j)) (γ : Multiset I)
    (h0 : β + ([i,j,l] : Multiset I) = γ)
    (h1 : β + ([j,i,l] : Multiset I) = γ)
    (h2 : β + ([j,l,i] : Multiset I) = γ)
    (h3 : β + ([l,j,i] : Multiset I) = γ)
    (h4 : β + ([i,l,j] : Multiset I) = γ)
    (h5 : β + ([l,i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h0 h1 (contentNormalizedLeft_mem D Sc i j l)) M z).comp
      ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h1 h2 (contentNormalizedRight_mem D Sc j i l)) M z).comp
        (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h2 h3 (contentNormalizedLeft_mem D Sc j l i)) M z)) =
    (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h0 h4 (contentNormalizedRight_mem D Sc i j l)) M z).comp
      ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h4 h5 (contentNormalizedLeft_mem D Sc i l j)) M z).comp
        (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h5 h3 (contentNormalizedRight_mem D Sc l i j)) M z)) := by
  apply BalancedInduction.hom_ext
  intro v h m
  rw [contentTripleTransform_tensor D Sc cutoff N
    (σ := [i,j,l]) (τ := [j,i,l]) (υ := [j,l,i]) (ω := [l,j,i])
    h0 h1 h2 h3
    (contentNormalizedLeft_mem D Sc i j l) (contentNormalizedRight_mem D Sc j i l) (contentNormalizedLeft_mem D Sc j l i) M z v h m]
  rw [contentTripleTransform_tensor D Sc cutoff N
    (σ := [i,j,l]) (τ := [i,l,j]) (υ := [l,i,j]) (ω := [l,j,i])
    h0 h4 h5 h3
    (contentNormalizedRight_mem D Sc i j l) (contentNormalizedLeft_mem D Sc i l j) (contentNormalizedRight_mem D Sc l i j) M z v h m]
  have hs : (D.parity i * D.parity l) * (D.parity j * D.parity l) +
      (D.parity i * D.parity j) *
        (D.parity i * D.parity l + D.parity j * D.parity l) =
      (D.parity i * D.parity l) * (D.parity i * D.parity j) +
      (D.parity j * D.parity l) *
        (D.parity i * D.parity l + D.parity i * D.parity j) := by ring
  have hp : D.parity i * D.parity j +
      (D.parity i * D.parity l + D.parity j * D.parity l) =
      D.parity j * D.parity l +
        (D.parity i * D.parity l + D.parity i * D.parity j) := by ring
  rw [hs, hp, contentNormalized_braid D Sc i j l hb]

section Braid
variable (β : Multiset I) (i j l : I) (hb : ¬ (i = l ∧ i ≠ j)) (γ : Multiset I)
  (h₀ : β + ([i,j,l] : Multiset I) = γ) (h₁ : β + ([j,i,l] : Multiset I) = γ)
  (h₂ : β + ([j,l,i] : Multiset I) = γ) (h₃ : β + ([l,j,i] : Multiset I) = γ)
  (h₄ : β + ([i,l,j] : Multiset I) = γ) (h₅ : β + ([l,i,j] : Multiset I) = γ)

include hb in
/-- The direct normalized operators satisfy the multicolour braid on every
module, with all six endpoint contents explicit and no comparison premise. -/
theorem contentInduction_uncorrected_braid (M : ContentModules D Sc cutoff N β) :
    ((contentInductionTransform D Sc cutoff N h₅ h₃ (contentNormalizedRight_mem D Sc l i j)).app (D.parity i * D.parity j) M) ≫
      ((contentInductionTransform D Sc cutoff N h₄ h₅ (contentNormalizedLeft_mem D Sc i l j)).app (D.parity i * D.parity l) M) ≫
      ((contentInductionTransform D Sc cutoff N h₀ h₄ (contentNormalizedRight_mem D Sc i j l)).app (D.parity j * D.parity l) M) =
    ((contentInductionTransform D Sc cutoff N h₂ h₃ (contentNormalizedLeft_mem D Sc j l i)).app (D.parity j * D.parity l) M) ≫
      ((contentInductionTransform D Sc cutoff N h₁ h₂ (contentNormalizedRight_mem D Sc j i l)).app (D.parity i * D.parity l) M) ≫
      ((contentInductionTransform D Sc cutoff N h₀ h₁ (contentNormalizedLeft_mem D Sc i j l)).app (D.parity i * D.parity j) M) := by
  apply moduleThree_eq_of_totals
    ((contentInductionTo D Sc cutoff N β [l,j,i] γ h₃).obj M)
    ((contentInductionTo D Sc cutoff N β [l,i,j] γ h₅).obj M)
    ((contentInductionTo D Sc cutoff N β [i,l,j] γ h₄).obj M)
    ((contentInductionTo D Sc cutoff N β [i,j,l] γ h₀).obj M)
    ((contentInductionTo D Sc cutoff N β [j,l,i] γ h₂).obj M)
    ((contentInductionTo D Sc cutoff N β [j,i,l] γ h₁).obj M)
    ((contentInductionTransform D Sc cutoff N h₅ h₃ (contentNormalizedRight_mem D Sc l i j)).app (D.parity i * D.parity j) M)
    ((contentInductionTransform D Sc cutoff N h₄ h₅ (contentNormalizedLeft_mem D Sc i l j)).app (D.parity i * D.parity l) M)
    ((contentInductionTransform D Sc cutoff N h₀ h₄ (contentNormalizedRight_mem D Sc i j l)).app (D.parity j * D.parity l) M)
    ((contentInductionTransform D Sc cutoff N h₂ h₃ (contentNormalizedLeft_mem D Sc j l i)).app (D.parity j * D.parity l) M)
    ((contentInductionTransform D Sc cutoff N h₁ h₂ (contentNormalizedRight_mem D Sc j i l)).app (D.parity i * D.parity l) M)
    ((contentInductionTransform D Sc cutoff N h₀ h₁ (contentNormalizedLeft_mem D Sc i j l)).app (D.parity i * D.parity j) M)
    (fun w => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h₅ h₃ (contentNormalizedRight_mem D Sc l i j)) M w)
    (fun w => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h₄ h₅ (contentNormalizedLeft_mem D Sc i l j)) M w)
    (fun w => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h₀ h₄ (contentNormalizedRight_mem D Sc i j l)) M w)
    (fun w => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h₂ h₃ (contentNormalizedLeft_mem D Sc j l i)) M w)
    (fun w => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h₁ h₂ (contentNormalizedRight_mem D Sc j i l)) M w)
    (fun w => BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N h₀ h₁ (contentNormalizedLeft_mem D Sc i j l)) M w)
  · intro w
    exact contentInductionTransform_total D Sc cutoff N h₅ h₃ (contentNormalizedRight_mem D Sc l i j) M w
  · intro w
    exact contentInductionTransform_total D Sc cutoff N h₄ h₅ (contentNormalizedLeft_mem D Sc i l j) M w
  · intro w
    exact contentInductionTransform_total D Sc cutoff N h₀ h₄ (contentNormalizedRight_mem D Sc i j l) M w
  · intro w
    exact contentInductionTransform_total D Sc cutoff N h₂ h₃ (contentNormalizedLeft_mem D Sc j l i) M w
  · intro w
    exact contentInductionTransform_total D Sc cutoff N h₁ h₂ (contentNormalizedRight_mem D Sc j i l) M w
  · intro w
    exact contentInductionTransform_total D Sc cutoff N h₀ h₁ (contentNormalizedLeft_mem D Sc i j l) M w
  · intro w
    exact (inductionLinear_braid D Sc cutoff N β i j l hb γ h₀ h₁ h₂ h₃ h₄ h₅ M w).symm
end Braid
end OddMath.QuiverHecke.ELVOld
