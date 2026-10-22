/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CategoricalDividedPowersDown
import OddMath.QuiverHecke.EvenDividedPowerExamples
import OddMath.QuiverHecke.AlgebraExamples

/-!
# Downward categorical divided-power consumers

BE2, arXiv:1701.04133v2, Lemma 11.5 for `F_i^{(n)}`: the corrected and printed class equations
for the even rank-one datum over `ZMod 2` in every rank, and for the datum with countably many
odd colours over `ℚ` in every rank at least two, at every weight.
-/

noncomputable section
namespace OddMath.QuiverHecke.CategoricalDividedPowersDownExamples
open CategoryTheory StringDiagrams LaurentPolynomial CategoricalDividedPowers
open OddMath.CoveringQuantum Categorification

example (r : ℕ) (ν : ℤ) :
    letI := K₀.moduleLaurentInt (ZMod 2) (HomCatDown EvenDividedPowerExamples.datum
      EvenDividedPowerExamples.scalars EvenDividedPowerExamples.symmetrizer
      EvenDividedPowerExamples.homogeneous () r ν)
    K₀.mk (OddMath.SKM.Summands.whole (downWordHom EvenDividedPowerExamples.datum
        EvenDividedPowerExamples.scalars EvenDividedPowerExamples.symmetrizer
        EvenDividedPowerExamples.homogeneous () r ν)) =
      QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit 1) r •
        K₀.mk (dividedPowerDownCorrected EvenDividedPowerExamples.datum
          EvenDividedPowerExamples.scalars EvenDividedPowerExamples.symmetrizer
          EvenDividedPowerExamples.homogeneous () rfl r ν) :=
  class_corrected_down _ _ _ _ () rfl r ν

example (i n : ℕ) (ν : ℕ → ℤ) :
    letI := K₀.moduleLaurent ℚ (HomCatDown AlgebraExamples.datum AlgebraExamples.scalars
      AlgebraExamples.symmetrizer AlgebraExamples.homogeneous i (n + 2) ν)
    K₀.mk (OddMath.SKM.Summands.whole (downWordHom AlgebraExamples.datum
        AlgebraExamples.scalars AlgebraExamples.symmetrizer AlgebraExamples.homogeneous i
        (n + 2) ν)) =
      qpFact (qUnitPi (AlgebraExamples.symmetrizer.d i)) piLP (n + 2) •
        K₀.mk (oddDividedPowerDownCorrected AlgebraExamples.datum AlgebraExamples.scalars
          AlgebraExamples.symmetrizer AlgebraExamples.homogeneous i rfl n ν) :=
  class_corrected_down_odd _ _ _ _ i rfl n ν

example (i n : ℕ) (ν : ℕ → ℤ) :
    letI := K₀.moduleLaurent ℚ (HomCatDown AlgebraExamples.datum AlgebraExamples.scalars
      AlgebraExamples.symmetrizer AlgebraExamples.homogeneous i (n + 2) ν)
    K₀.mk (OddMath.SKM.Summands.whole (downWordHom AlgebraExamples.datum
        AlgebraExamples.scalars AlgebraExamples.symmetrizer AlgebraExamples.homogeneous i
        (n + 2) ν)) =
      (T (-(((n + 2).choose 2 : ℤ) * AlgebraExamples.symmetrizer.d i)) *
        qpFact (qUnitPi (AlgebraExamples.symmetrizer.d i)) piLP (n + 2)) •
        K₀.mk (oddDividedPowerDownPrinted AlgebraExamples.datum AlgebraExamples.scalars
          AlgebraExamples.symmetrizer AlgebraExamples.homogeneous i rfl n ν) :=
  class_printed_down_odd _ _ _ _ i rfl n ν

end OddMath.QuiverHecke.CategoricalDividedPowersDownExamples
