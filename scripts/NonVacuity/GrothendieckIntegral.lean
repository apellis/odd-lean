import OddMath

/-! # BE2 Theorem 11.7 (existence of `γ` on the `ℒ`-form), on a concrete datum

The two-odd-colour rational datum of `OddMath.SKM.LaurentianK0Examples`, where every hypothesis
of `QuiverHecke.SerreComplex.theorem_11_7_existence` is proved.
-/

noncomputable section
namespace NonVacuity.GrothendieckIntegral
open CategoryTheory StringDiagrams LaurentPolynomial OddMath OddMath.QuiverHecke.SerreComplex
open OddMath.SKM.LaurentianK0Examples OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
open OddMath.SKM.DimensionFormulaExamples

/-- The homomorphism `γ` on the `ℒ`-form. -/
example := gammaInt twoOddDatum homogeneous cScalars locallyFinite

/-- Existence and uniqueness. -/
example := theorem_11_7_existence twoOddDatum homogeneous cScalars locallyFinite

/-- `e_i^{(2)} 1_0 ↦ [E_i^{(2)} 1_0]`. -/
example := gammaInt_edp twoOddDatum homogeneous cScalars locallyFinite true 2 0

/-- `ℚ(q)[π]/(π² - 1)` is a localization of `ℤ[q, q⁻¹, π]/(π² - 1)`. -/
example := OddMath.CoveringQuantum.Coefficients.isLocalization

#print axioms OddMath.QuiverHecke.SerreComplex.theorem_11_7_existence
#print axioms OddMath.CoveringQuantum.Coefficients.isLocalization
#print axioms OddMath.CoveringQuantum.UDot.lFormHom

end NonVacuity.GrothendieckIntegral
