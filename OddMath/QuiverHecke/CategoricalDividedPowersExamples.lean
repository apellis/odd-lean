/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CategoricalDividedPowers
import OddMath.QuiverHecke.EvenDividedPowerExamples

/-!
# Even categorical divided-power consumers

BE2, arXiv:1701.04133v2, Lemma 11.5 for the even rank-one datum over `ZMod 2`, in every rank and
at every weight: the printed and corrected class equations.
-/

noncomputable section
namespace OddMath.QuiverHecke.CategoricalDividedPowersExamples
open CategoryTheory StringDiagrams LaurentPolynomial CategoricalDividedPowers
open EvenDividedPowerExamples Categorification

example (r : ℕ) (ν : ℤ) :
    letI := K₀.moduleLaurentInt (ZMod 2) (HomCat datum scalars symmetrizer homogeneous () r ν)
    K₀.mk (OddMath.SKM.Summands.whole (upWordHom datum scalars symmetrizer homogeneous () r ν)) =
      QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit 1) r •
        K₀.mk (dividedPowerCorrected datum scalars symmetrizer homogeneous () rfl r ν) :=
  class_corrected datum scalars symmetrizer homogeneous () rfl r ν

example (r : ℕ) (ν : ℤ) :
    letI := K₀.moduleLaurentInt (ZMod 2) (HomCat datum scalars symmetrizer homogeneous () r ν)
    K₀.mk (OddMath.SKM.Summands.whole (upWordHom datum scalars symmetrizer homogeneous () r ν)) =
      (T ((r.choose 2 : ℤ) * 1) * QuantumGroup.qfact (K := LaurentPolynomial ℤ) (qUnit 1) r) •
        K₀.mk (dividedPowerPrinted datum scalars symmetrizer homogeneous () rfl r ν) :=
  class_printed datum scalars symmetrizer homogeneous () rfl r ν

end OddMath.QuiverHecke.CategoricalDividedPowersExamples
