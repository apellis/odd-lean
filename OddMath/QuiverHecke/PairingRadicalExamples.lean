/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.PairingRadical
import OddMath.SKM.DimensionFormulaExamples

/-!
# Relations among classes of words lie in the radical: consumers

For the datum with two odd colours and rational scalars: the pairing of two words evaluated at
`π = -1` is the Laurent expansion of the form at `π = -1`, and the radical criterion applies to
a combination of words (here the empty one, whose class vanishes).
-/

noncomputable section
namespace OddMath.QuiverHecke.PairingRadicalExamples
open CategoryTheory StringDiagrams CoveringQuantum
open CoveringQuantum.UDot.ContextualExchangeExamples SKM.DimensionFormulaExamples

example : evalSeries (-1) (by norm_num) (GSKar.pairing ℚ
        (homBoundedBelow twoOddDatum.toSKM twoOddDatum.skmSymmetrizer scalars homogeneous)
        (GSKar.of ℚ (hObj twoOddDatum.toSKM scalars twoOddDatum.skmSymmetrizer homogeneous
          [true, false]) 0 0)
        (K₀.mk (GSKar.of ℚ (hObj twoOddDatum.toSKM scalars twoOddDatum.skmSymmetrizer homogeneous
          [false, true]) 0 0))) =
      signLaurent ((-1 : ℤ) : ℚ) (by norm_num)
        (twoOddDatum.toSuperCartanDatum.form Coefficients.q Coefficients.pi
          (PreF.monomial Coefficients.Ring [true, false])
          (PreF.monomial Coefficients.Ring [false, true])) :=
  evalSeries_pairing_word twoOddDatum scalars homogeneous (-1) (by norm_num) _ _

example : ((0 : List Bool →₀ LaurentPolynomial Zπ).sum fun t r =>
      Coefficients.ofLaurent r • PreF.monomial Coefficients.Ring t) ∈
      PreF.radical (twoOddDatum.toSuperCartanDatum.chi Coefficients.q Coefficients.pi)
        (twoOddDatum.toSuperCartanDatum.norm Coefficients.q Coefficients.pi) :=
  mem_radical_of_wordSum_eq_zero twoOddDatum scalars homogeneous 0 (by simp)

end OddMath.QuiverHecke.PairingRadicalExamples
