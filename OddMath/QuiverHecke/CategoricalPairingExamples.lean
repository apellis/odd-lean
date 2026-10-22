/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CategoricalPairing
import OddMath.SKM.DimensionFormulaExamples

/-!
# The categorical pairing of words is the form: consumers

For the datum with two odd colours and rational scalars, at both signs of `π`: the graded
dimension pairing of two words in `K₀(Ḣ_{q,π})` has the coefficients of the form on the free
algebra.
-/

noncomputable section
namespace OddMath.QuiverHecke.CategoricalPairingExamples
open CategoryTheory StringDiagrams CoveringQuantum
open CoveringQuantum.UDot.ContextualExchangeExamples SKM.DimensionFormulaExamples

example (σ : ℤ) (hσ : σ * σ = 1) (z : ℤ) :
    ((Zπ.eval σ hσ ((GSKar.pairing ℚ
        (homBoundedBelow twoOddDatum.toSKM twoOddDatum.skmSymmetrizer scalars homogeneous)
        (GSKar.of ℚ (hObj twoOddDatum.toSKM scalars twoOddDatum.skmSymmetrizer homogeneous
          [true, false]) 0 0)
        (K₀.mk (GSKar.of ℚ (hObj twoOddDatum.toSKM scalars twoOddDatum.skmSymmetrizer homogeneous
          [false, true]) 0 0))).coeff z) : ℤ) : ℚ) =
      (signLaurent (σ : ℚ) (by rw [pow_two]; exact_mod_cast hσ)
        (twoOddDatum.toSuperCartanDatum.form Coefficients.q Coefficients.pi
          (PreF.monomial Coefficients.Ring [true, false])
          (PreF.monomial Coefficients.Ring [false, true]))).coeff z :=
  pairing_word_eq_form twoOddDatum scalars homogeneous σ hσ _ _ z

example (z : ℤ) :
    ((Zπ.eval (-1) (by norm_num) ((GSKar.pairing ℚ
        (homBoundedBelow twoOddDatum.toSKM twoOddDatum.skmSymmetrizer scalars homogeneous)
        (GSKar.of ℚ (hObj twoOddDatum.toSKM scalars twoOddDatum.skmSymmetrizer homogeneous
          [true, true]) 0 0)
        (K₀.mk (GSKar.of ℚ (hObj twoOddDatum.toSKM scalars twoOddDatum.skmSymmetrizer homogeneous
          [true, true]) 0 0))).coeff z) : ℤ) : ℚ) =
      (signLaurent ((-1 : ℤ) : ℚ) (by norm_num)
        (twoOddDatum.toSuperCartanDatum.form Coefficients.q Coefficients.pi
          (PreF.monomial Coefficients.Ring [true, true])
          (PreF.monomial Coefficients.Ring [true, true]))).coeff z :=
  pairing_word_eq_form twoOddDatum scalars homogeneous (-1) (by norm_num) _ _ z

end OddMath.QuiverHecke.CategoricalPairingExamples
