import OddMath.QuiverHecke.CyclotomicAction.ELVTripleCorrectionPolynomial

/-! # The original-parameter source correction at an explicit output content

Brundan--Ellis (1.9), repeated outer colour. Retain the common output γ
and all word-content equalities while applying the checked source
polynomial identity. This avoids replacing a native output module by a
separately normalized canonical-content model.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
local notation "Sc'" => parameterTwist D Sc

/-- The normalized source mixed braid equals the ORIGINAL Sc ordered
polynomial at a specified output content, with all three word endpoints explicit. -/
theorem contentMixedBraid_at_polynomial
    (β : Multiset I) (i j : I) (hij : i ≠ j) (γ : Multiset I)
    (h₀ : β + ([i,j,i] : Multiset I) = γ)
    (h₁ : β + ([i,i,j] : Multiset I) = γ)
    (h₂ : β + ([j,i,i] : Multiset I) = γ)
    (M : ContentModules D Sc' cutoff bound β) (w : ContentCategory D Sc' cutoff bound γ) :
    let T0 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₁ (contentTripleRight_parity D Sc' i j i)) M w
    let T1 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₁ h₁ (contentTripleLeft_parity D Sc' i i j)) M w
    let T2 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₁ h₀ (contentTripleRight_parity D Sc' i i j)) M w
    let T3 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₂ (contentTripleLeft_parity D Sc' i j i)) M w
    let T4 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₂ h₂ (contentTripleRight_parity D Sc' j i i)) M w
    let T5 := BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc' cutoff bound h₂ h₀ (contentTripleLeft_parity D Sc' j i i)) M w
    T0.comp ((-T1).comp T2) - T3.comp ((-T4).comp T5) =
      tripleDotCorrectionPolynomial D Sc i j
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (firstDot_parity D Sc' i [j,i])) M w)
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (contentTripleDot_one_parity D Sc' i j)) M w)
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc' cutoff bound h₀ h₀ (contentTripleDot_two_parity D Sc' i j)) M w) := by
  cases h₀
  have hs := contentMixedBraid_polynomial_linear D Sc cutoff bound β hij M w
  have hp := contentMixedBraidPolynomial_eq_ordered D Sc cutoff bound β i j M w
  exact hs.trans hp

end OddMath.QuiverHecke.ELVOld
