import OddMath

/-! Non-vacuity checks in `NonVacuity.Claim5CapCoefficients`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.Claim5CapCoefficients

-- Complete families, independent serializers, and a populated degree-19 fibre.
example (ε : Bool) := OddMath.SKM.CapFamilyCoefficientsExamples.family_coefficients ε

-- Odd weight two distinguishes the corrected scalar from the printed expression.
example := OddMath.CoveringQuantum.CapScalarExamples.odd_two_ne_unbarred
example := OddMath.CoveringQuantum.CapScalarExamples.odd_two_minus_coeff
example := OddMath.CoveringQuantum.CapScalarExamples.odd_two_shifted_coeff

end NonVacuity.Claim5CapCoefficients
