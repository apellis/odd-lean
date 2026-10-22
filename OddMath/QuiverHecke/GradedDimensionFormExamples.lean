/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.GradedDimensionForm
import OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples

/-!
# Graded dimensions of `Hom_H` and the form: consumers

For the datum with one odd simple root, at both signs of `π`: the coefficients of the form
`(θ_t, θ_{t'})` count the normal forms of `H` of each degree, for a repeated odd word and for
words of different lengths.
-/

noncomputable section
namespace OddMath.QuiverHecke.GradedDimensionFormExamples
open CoveringQuantum SKM.PositiveDecoratedFamilyCoefficientsExamples

example (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (signLaurent σ hσ (oddDatum.toSuperCartanDatum.form Coefficients.q Coefficients.pi
      (PreF.monomial Coefficients.Ring [(), ()])
      (PreF.monomial Coefficients.Ring [(), ()]))).coeff z =
      ∑ i ∈ (finite_deg_eq oddDatum.toSKM oddDatum.skmSymmetrizer [(), ()] [(), ()] z).toFinset,
        σ ^ (i.par oddDatum.toSKM).val :=
  coeff_form_eq_sum_fiber oddDatum σ hσ _ _ z

example (z : ℤ) :
    (signLaurent (-1) (by norm_num) (oddDatum.toSuperCartanDatum.form Coefficients.q
      Coefficients.pi (PreF.monomial Coefficients.Ring [()])
      (PreF.monomial Coefficients.Ring [(), ()]))).coeff z =
      ∑ i ∈ (finite_deg_eq oddDatum.toSKM oddDatum.skmSymmetrizer [()] [(), ()] z).toFinset,
        (-1 : ℚ) ^ (i.par oddDatum.toSKM).val :=
  coeff_form_eq_sum_fiber oddDatum (-1) (by norm_num) _ _ z

end OddMath.QuiverHecke.GradedDimensionFormExamples
