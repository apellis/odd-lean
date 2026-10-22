/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CategoricalDividedPowersOdd
import OddMath.QuiverHecke.AlgebraExamples

/-!
# Odd categorical divided-power consumers

BE2, arXiv:1701.04133v2, Lemma 11.5 for the datum with countably many odd colours over `ℚ`,
in every rank at least two, for every colour and at every weight: the printed and corrected
class equations.
-/

noncomputable section
namespace OddMath.QuiverHecke.CategoricalDividedPowersOddExamples
open CategoryTheory StringDiagrams LaurentPolynomial CategoricalDividedPowers
open AlgebraExamples OddMath.CoveringQuantum

example (i n : ℕ) (ν : ℕ → ℤ) :
    letI := K₀.moduleLaurent ℚ (HomCat datum scalars symmetrizer homogeneous i (n + 2) ν)
    K₀.mk (OddMath.SKM.Summands.whole
        (upWordHom datum scalars symmetrizer homogeneous i (n + 2) ν)) =
      qpFact (qUnitPi (symmetrizer.d i)) piLP (n + 2) •
        K₀.mk (oddDividedPowerCorrected datum scalars symmetrizer homogeneous i rfl n ν) :=
  class_corrected_odd datum scalars symmetrizer homogeneous i rfl n ν

example (i n : ℕ) (ν : ℕ → ℤ) :
    letI := K₀.moduleLaurent ℚ (HomCat datum scalars symmetrizer homogeneous i (n + 2) ν)
    K₀.mk (OddMath.SKM.Summands.whole
        (upWordHom datum scalars symmetrizer homogeneous i (n + 2) ν)) =
      (T (((n + 2).choose 2 : ℤ) * symmetrizer.d i) * piLP ^ (n + 2).choose 2 *
        qpFact (qUnitPi (symmetrizer.d i)) piLP (n + 2)) •
        K₀.mk (oddDividedPowerPrinted datum scalars symmetrizer homogeneous i rfl n ν) :=
  class_printed_odd datum scalars symmetrizer homogeneous i rfl n ν

end OddMath.QuiverHecke.CategoricalDividedPowersOddExamples
