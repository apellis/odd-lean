/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.EnvelopeDividedPowers
import OddMath.QuiverHecke.EvenDividedPowerExamples
import OddMath.QuiverHecke.AlgebraExamples

/-!
# Lemma 11.1 in `K₀(Ḣ_{q,π})`: consumers

BE2, arXiv:1701.04133v2, Lemma 11.1 read in the envelope `Ḣ_{q,π}`, for the even rank-one datum
over `ZMod 2` in every rank, and for the datum with countably many odd colours over `ℚ` in every
rank at least two, for every colour.
-/

noncomputable section
namespace OddMath.QuiverHecke.EnvelopeDividedPowersExamples
open CategoryTheory StringDiagrams LaurentPolynomial CategoricalDividedPowers
open OddMath.CoveringQuantum Categorification

example (r : ℕ) :
    letI := K₀.moduleLaurentInt (ZMod 2) (HKar (k := ZMod 2) EvenDividedPowerExamples.datum
      EvenDividedPowerExamples.scalars EvenDividedPowerExamples.symmetrizer
      EvenDividedPowerExamples.homogeneous)
    K₀.mk (word EvenDividedPowerExamples.datum EvenDividedPowerExamples.scalars
        EvenDividedPowerExamples.symmetrizer EvenDividedPowerExamples.homogeneous
        (List.replicate r ())) =
      QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit 1) r •
        K₀.mk (dividedPowerEven EvenDividedPowerExamples.datum EvenDividedPowerExamples.scalars
          EvenDividedPowerExamples.symmetrizer EvenDividedPowerExamples.homogeneous () rfl r) :=
  class_word_even _ _ _ _ () rfl r

example (i n : ℕ) :
    letI := K₀.moduleLaurent ℚ (HKar (k := ℚ) AlgebraExamples.datum AlgebraExamples.scalars
      AlgebraExamples.symmetrizer AlgebraExamples.homogeneous)
    K₀.mk (word AlgebraExamples.datum AlgebraExamples.scalars AlgebraExamples.symmetrizer
        AlgebraExamples.homogeneous (List.replicate (n + 2) i)) =
      qpFact (qUnitPi (AlgebraExamples.symmetrizer.d i)) piLP (n + 2) •
        K₀.mk (dividedPowerOdd AlgebraExamples.datum AlgebraExamples.scalars
          AlgebraExamples.symmetrizer AlgebraExamples.homogeneous i rfl n) :=
  class_word_odd _ _ _ _ i rfl n

end OddMath.QuiverHecke.EnvelopeDividedPowersExamples
