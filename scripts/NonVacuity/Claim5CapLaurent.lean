import OddMath

/-! Non-vacuity checks in `NonVacuity.Claim5CapLaurent`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.Claim5CapLaurent

-- Both orientations, with the shorter-series premise proved for an explicit dot series.
example := OddMath.SKM.CapLaurentCoefficientsExamples.family_laurent_coefficients true
example := OddMath.SKM.CapLaurentCoefficientsExamples.family_laurent_coefficients false

-- Three shorter dots give nonzero degree-14 coefficients at both signs.
example := OddMath.SKM.CapLaurentCoefficientsExamples.shorter_three_dots

end NonVacuity.Claim5CapLaurent
