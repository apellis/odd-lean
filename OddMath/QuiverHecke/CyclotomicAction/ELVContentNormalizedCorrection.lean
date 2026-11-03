import OddMath.QuiverHecke.CyclotomicAction.ELVContentCorrectionCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVContentUncorrectedBraid

/-! # Normalized mixed braid correction on direct word induction

Brundan--Ellis (1.9). Keep the independently prescribed equal-colour
minus signs and all intermediate word contents in the corrected relation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

private theorem transform_congr {β γ : Multiset I} {σ τ : List I} {p : ZMod 2}
    (h : β + (σ : Multiset I) = γ) (ht : β + (τ : Multiset I) = γ)
    {f g : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hf : f ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ p) (hfg : f = g)
    (M : ContentModules D Sc cutoff bound β) (w : ContentCategory D Sc cutoff bound γ) :
    BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff bound h ht hf) M w =
      BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff bound h ht hg) M w := by
  cases hfg
  rfl

private theorem transform_neg {β γ : Multiset I} {σ τ : List I} {p : ZMod 2}
    (h : β + (σ : Multiset I) = γ) (ht : β + (τ : Multiset I) = γ)
    {f : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hf : f ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff bound β) (w : ContentCategory D Sc cutoff bound γ) :
    BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff bound h ht (Submodule.neg_mem _ hf)) M w =
      -BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff bound h ht hf) M w := by
  apply BalancedInduction.hom_ext
  intro v a m
  simp only [BalancedInduction.transformLinear_tensor, contentAppendToComponent_neg,
    Preadditive.neg_comp, LinearMap.neg_apply]
  simp only [BalancedInduction.tensor, TensorProduct.neg_tmul, map_neg]

private theorem normalized_left_distinct (i j l : I) (hij : i ≠ j) :
    contentNormalizedLeft D Sc i j l = contentTripleLeft D Sc i j l := by
  classical
  simp only [contentNormalizedLeft, contentTriplePrefixAffine, ite_eq_right hij]
private theorem normalized_left_equal (i l : I) :
    contentNormalizedLeft D Sc i i l = -contentTripleLeft D Sc i i l := by
  classical
  simp only [contentNormalizedLeft, contentTriplePrefixAffine, ite_true]
private theorem normalized_right_distinct (i j l : I) (hjl : j ≠ l) :
    contentNormalizedRight D Sc i j l = contentTripleRight D Sc i j l := by
  rw [contentNormalizedRight, contentCrossAffine_distinct D Sc j l hjl,
    contentTripleRight_whisker]
private theorem normalized_right_equal (j i : I) :
    contentNormalizedRight D Sc j i i = -contentTripleRight D Sc j i i := by
  rw [contentNormalizedRight, contentCrossAffine_equal,
    MonoidalSupercategory.whiskerLeft_neg (R := k), contentTripleRight_whisker]

local notation "Sc'" => parameterTwist D Sc

/-- Direct normalized crossing paths with a repeated outer colour differ
by the ordered correction in the original parameter family Sc. -/
theorem contentNormalizedMixedBraid_at_polynomial
    (β : Multiset I) (i j : I) (hij : i ≠ j) (γ : Multiset I)
    (h₀ : β + ([i,j,i] : Multiset I) = γ)
    (h₁ : β + ([i,i,j] : Multiset I) = γ)
    (h₂ : β + ([j,i,i] : Multiset I) = γ)
    (M : ContentModules D Sc' cutoff bound β) (w : ContentCategory D Sc' cutoff bound γ) :
    let T0 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₁ (contentNormalizedRight_mem D Sc' i j i)) M w
    let T1 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₁ h₁ (contentNormalizedLeft_mem D Sc' i i j)) M w
    let T2 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₁ h₀ (contentNormalizedRight_mem D Sc' i i j)) M w
    let T3 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₂ (contentNormalizedLeft_mem D Sc' i j i)) M w
    let T4 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₂ h₂ (contentNormalizedRight_mem D Sc' j i i)) M w
    let T5 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₂ h₀ (contentNormalizedLeft_mem D Sc' j i i)) M w
    T0.comp (T1.comp T2) - T3.comp (T4.comp T5) =
      tripleDotCorrectionPolynomial D Sc i j
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (firstDot_parity D Sc' i [j,i])) M w)
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (contentTripleDot_one_parity D Sc' i j)) M w)
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (contentTripleDot_two_parity D Sc' i j)) M w) := by
  dsimp only
  have h0 := transform_congr D Sc' cutoff bound h₀ h₁
    (contentNormalizedRight_mem D Sc' i j i) (contentTripleRight_parity D Sc' i j i)
    (normalized_right_distinct D Sc' i j i hij.symm) M w
  have h1 := transform_congr D Sc' cutoff bound h₁ h₁
    (contentNormalizedLeft_mem D Sc' i i j) (Submodule.neg_mem _ (contentTripleLeft_parity D Sc' i i j))
    (normalized_left_equal D Sc' i j) M w
  have hn1 := transform_neg D Sc' cutoff bound h₁ h₁ (contentTripleLeft_parity D Sc' i i j) M w
  have he1 := h1.trans hn1
  have h2 := transform_congr D Sc' cutoff bound h₁ h₀
    (contentNormalizedRight_mem D Sc' i i j) (contentTripleRight_parity D Sc' i i j)
    (normalized_right_distinct D Sc' i i j hij) M w
  have h3 := transform_congr D Sc' cutoff bound h₀ h₂
    (contentNormalizedLeft_mem D Sc' i j i) (contentTripleLeft_parity D Sc' i j i)
    (normalized_left_distinct D Sc' i j i hij) M w
  have h4 := transform_congr D Sc' cutoff bound h₂ h₂
    (contentNormalizedRight_mem D Sc' j i i) (Submodule.neg_mem _ (contentTripleRight_parity D Sc' j i i))
    (normalized_right_equal D Sc' j i) M w
  have hn4 := transform_neg D Sc' cutoff bound h₂ h₂ (contentTripleRight_parity D Sc' j i i) M w
  have he4 := h4.trans hn4
  have h5 := transform_congr D Sc' cutoff bound h₂ h₀
    (contentNormalizedLeft_mem D Sc' j i i) (contentTripleLeft_parity D Sc' j i i)
    (normalized_left_distinct D Sc' j i i hij.symm) M w
  rw [h0, he1, h2, h3, he4, h5]
  exact contentMixedBraid_at_polynomial D Sc cutoff bound β i j hij γ h₀ h₁ h₂ M w

end OddMath.QuiverHecke.ELVOld
