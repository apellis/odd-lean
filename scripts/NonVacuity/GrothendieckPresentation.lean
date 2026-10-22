import OddMath

/-! # The homomorphism `γ` of BE2 Theorem 11.7 over `ℒ`, on a concrete datum

The two-odd-colour rational datum of `OddMath.SKM.LaurentianK0Examples`: the relations (9.2)–(9.4)
in the Grothendieck ring at the weight `0`, and the homomorphism `gammaL` with its values on
generators.
-/

noncomputable section
namespace NonVacuity.GrothendieckPresentation
open CategoryTheory StringDiagrams LaurentPolynomial OddMath OddMath.QuiverHecke.SerreComplex
open OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
open OddMath.SKM.DimensionFormulaExamples

/-- The `ℒ`-algebra homomorphism from `U̇_{q,π}(𝔤)`. -/
example := gammaL twoOddDatum homogeneous

example (μ : Bool → ℤ) :=
  gammaL_E twoOddDatum homogeneous true μ

/-- (9.2) for two distinct colours and for one colour. -/
example := comm_gr (Sc := scalars) twoOddDatum.skmSymmetrizer homogeneous true false 0

example := comm_gr (Sc := scalars) twoOddDatum.skmSymmetrizer homogeneous true true 0

/-- (9.3) and (9.4) for `i = true`, `j = false`. -/
example := serreE_sum (Sc := scalars) twoOddDatum.skmSymmetrizer homogeneous true false
  (twoOddDatum.serreDeg true false) 0 (by decide) (serreDeg_eq twoOddDatum (by decide))

example := serreF_sum (Sc := scalars) twoOddDatum.skmSymmetrizer homogeneous true false
  (twoOddDatum.serreDeg true false) 0 (by decide) (serreDeg_eq twoOddDatum (by decide))

#print axioms OddMath.QuiverHecke.SerreComplex.gammaL
#print axioms OddMath.QuiverHecke.SerreComplex.gammaL_epow
#print axioms OddMath.QuiverHecke.SerreComplex.serreF_sum

end NonVacuity.GrothendieckPresentation
