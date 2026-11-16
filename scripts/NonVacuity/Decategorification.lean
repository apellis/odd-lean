import OddMath
import NonVacuity.GroundRingNondegeneracy

/-! # The Decategorification Conjecture on a concrete datum

The two-odd-colour rational datum of `OddMath.SKM.LaurentianK0Examples`, with the scalars of
`OddMath.SKM.DimensionFormulaExamples`, over `ℚ`. Every hypothesis of
`QuiverHecke.SerreComplex.decategorification` is proved here.
-/

noncomputable section
namespace NonVacuity.Decategorification
open OddMath OddMath.SKM OddMath.QuiverHecke.SerreComplex
open OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
open OddMath.SKM.LaurentianK0Examples OddMath.SKM.DimensionFormulaExamples
open OddMath.SKM.Theorem103Examples

/-- `γ` is bijective for the two-odd-colour datum over `ℚ`. -/
example : Function.Bijective (gammaInt twoOddDatum homogeneous cScalars
    (twoOddDatum.skmSymmetrizer.degreeLocallyFinite_of_finite)) :=
  decategorification twoOddDatum homogeneous cScalars _ two_ne_zero
    NonVacuity.GroundRingNondegeneracy.twoOdd_root_independent
    NonVacuity.GroundRingNondegeneracy.twoOdd_coroot_independent

#print axioms OddMath.QuiverHecke.SerreComplex.decategorification

end NonVacuity.Decategorification
