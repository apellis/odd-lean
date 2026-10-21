import OddMath

/-! Non-vacuity checks in `NonVacuity.AdjointCoefficients`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.AdjointCoefficients
open OddMath.CoveringQuantum UDot UDot.GenericTensor Coefficients PreF
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.SKM.PositiveFormCoefficientsExamples

example :
    (signLaurent 1 (by norm_num) (sesquilinearForm oddDatum
      (positiveHalf oddDatum Coefficients.q pi 0
        (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [()])))
      (⟨F oddDatum Coefficients.q pi () 4,
        F_mem_modified oddDatum Coefficients.q pi () 4⟩ *
        positiveHalf oddDatum Coefficients.q pi 0
          (oddDatum.toSerreF Coefficients.q pi
            (monomial Coefficients.Ring [(), ()]))))).coeff 1 = 1 ∧
    (signLaurent (-1) (by norm_num) (sesquilinearForm oddDatum
      (positiveHalf oddDatum Coefficients.q pi 0
        (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [()])))
      (⟨F oddDatum Coefficients.q pi () 4,
        F_mem_modified oddDatum Coefficients.q pi () 4⟩ *
        positiveHalf oddDatum Coefficients.q pi 0
          (oddDatum.toSerreF Coefficients.q pi
            (monomial Coefficients.Ring [(), ()]))))).coeff 1 = -1 :=
  OddMath.CoveringQuantum.UDot.AdjointCoefficientsExamples.repeated_odd_physical_both_signs

example (σ : ℚ) (hσ : σ ^ 2 = 1) :
    (signLaurent σ hσ (sesquilinearForm oddDatum
      (positiveHalf oddDatum Coefficients.q pi 0
        (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [()])))
      (⟨F oddDatum Coefficients.q pi () 4,
        F_mem_modified oddDatum Coefficients.q pi () 4⟩ *
        positiveHalf oddDatum Coefficients.q pi 0
          (oddDatum.toSerreF Coefficients.q pi
            (monomial Coefficients.Ring [(), ()]))))).coeff 1 = σ :=
  OddMath.CoveringQuantum.UDot.AdjointCoefficientsExamples.repeated_odd_bent_coeff σ hσ

end NonVacuity.AdjointCoefficients
