import OddMath

/-! Non-vacuity checks in `NonVacuity.Theorem103`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.Theorem103

-- Actual covering-ring equality for mixed boundaries and arbitrary external weights.
example (ε : Bool) (ζ μ : Bool → ℤ) :=
  OddMath.SKM.Theorem103Examples.graphical ε ζ μ
example := OddMath.SKM.Theorem103Examples.unequal_weight_zero true
example := OddMath.SKM.Theorem103Examples.unequal_weight_zero false

-- Both head orientations and both signs, with actually populated decorated fibres.
example (μ : Bool → ℤ) (z : ℤ) := OddMath.SKM.Theorem103Examples.both_signs true μ z
example (μ : Bool → ℤ) (z : ℤ) := OddMath.SKM.Theorem103Examples.both_signs false μ z
example (μ : Bool → ℤ) := OddMath.SKM.Theorem103Examples.populated true μ
example (μ : Bool → ℤ) := OddMath.SKM.Theorem103Examples.populated false μ

end NonVacuity.Theorem103
