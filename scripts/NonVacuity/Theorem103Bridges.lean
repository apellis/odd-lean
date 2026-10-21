import OddMath

/-! Non-vacuity checks in `NonVacuity.Theorem103Bridges`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.Theorem103Bridges

-- Arbitrary-word induction with no supplied shorter-word comparison or family-existence premise.
example (μ : Bool → ℤ) (z : ℤ) :=
  OddMath.SKM.EmptyBoundaryCoefficientsExamples.nested_both_signs μ z
example := OddMath.SKM.EmptyBoundaryCoefficientsExamples.nested_family_nonempty
example (μ : Bool → ℤ) (z : ℤ) :=
  OddMath.SKM.EmptyBoundaryCoefficientsExamples.distinct_coeff μ (-1) (by norm_num) z

-- Independent graphical expression, both signs and both cap orientations, populated dot fibres.
example := OddMath.SKM.GraphicalSeriesExamples.Cap.both_signs true
example := OddMath.SKM.GraphicalSeriesExamples.Cap.both_signs false
example := OddMath.SKM.GraphicalSeriesExamples.Cap.populated true
example := OddMath.SKM.GraphicalSeriesExamples.Cap.populated false
example := OddMath.SKM.GraphicalSeriesExamples.TwoStrands.both_signs
example := OddMath.SKM.GraphicalSeriesExamples.TwoStrands.populated

end NonVacuity.Theorem103Bridges
