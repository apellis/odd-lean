import OddMath

/-! Non-vacuity checks in `NonVacuity.Claim5Algebra`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.Claim5Algebra
open OddMath.CoveringQuantum UDot Coefficients GenericTensor GenericVerma.MixedGram
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.SKM.PositiveFormCoefficientsExamples
open UDot.ContextualCommutatorExamples

example :
    sesquilinearForm oddDatum
      (algebraWord oddDatum 0 [(false, ()), (true, ()), (false, ()), (true, ())])
      (algebraWord oddDatum 0 []) -
    Coefficients.pi * sesquilinearForm oddDatum
      (algebraWord oddDatum 0 [(false, ()), (false, ()), (true, ()), (true, ())])
      (algebraWord oddDatum 0 []) =
    (((Coefficients.q⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring) +
      Coefficients.pi * (Coefficients.q : Coefficients.Ring)) *
      sesquilinearForm oddDatum
        (algebraWord oddDatum 0 [(false, ()), (true, ())]) (algebraWord oddDatum 0 []) :=
  odd_context_commutator

example :
    sesquilinearForm oddDatum
      (algebraWord oddDatum 2 [(true, ()), (false, ())]) (algebraWord oddDatum 2 []) -
    Coefficients.pi * sesquilinearForm oddDatum
      (algebraWord oddDatum 2 [(false, ()), (true, ())]) (algebraWord oddDatum 2 []) ≠
    qpInt Coefficients.q Coefficients.pi 2 := odd_unbarred_commutator_false

example : bar (qpInt Coefficients.q Coefficients.pi 2) ≠
    qpInt Coefficients.q Coefficients.pi 2 := odd_two_bar_ne

end NonVacuity.Claim5Algebra
