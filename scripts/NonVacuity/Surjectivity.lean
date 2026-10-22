import OddMath

/-! # BE2 Theorem 11.7 (surjectivity of `γ`), on a concrete datum

The two-odd-colour rational datum of `OddMath.SKM.LaurentianK0Examples`, where every hypothesis
of `QuiverHecke.theorem_11_7_surjective` is proved.
-/

noncomputable section
namespace NonVacuity.Surjectivity
open OddMath OddMath.SKM.LaurentianK0Examples
open OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
open OddMath.SKM.DimensionFormulaExamples

/-- `γ` is surjective. -/
example := QuiverHecke.theorem_11_7_surjective twoOddDatum homogeneous cScalars locallyFinite

#print axioms OddMath.QuiverHecke.theorem_11_7_surjective

end NonVacuity.Surjectivity
