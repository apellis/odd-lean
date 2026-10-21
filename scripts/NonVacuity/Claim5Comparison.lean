import OddMath

/-! Non-vacuity checks in `NonVacuity.Claim5Comparison`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.Claim5Comparison

-- Full coefficientwise iff with the shorter-word premise discharged at nonzero weight.
example := OddMath.SKM.Claim5CoefficientsExamples.form_coeff_iff (fun _ => 2)

-- Complete families in a nonempty context, with an independently specified shorter series.
example := OddMath.SKM.Claim5CoefficientsExamples.graphical_commutator 1 (by norm_num) 19
example := OddMath.SKM.Claim5CoefficientsExamples.graphical_commutator (-1) (by norm_num) 19

end NonVacuity.Claim5Comparison
