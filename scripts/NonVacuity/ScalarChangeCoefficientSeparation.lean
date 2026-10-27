import OddMath.SKM.ScalarChangeCoefficientSeparation
import OddMath.SKM.MixedCrossingLocalExamples
import Mathlib.Algebra.Ring.Prod

/-! Brundan–Ellis (1.21)–(1.22): a noninjective scalar map preserves
full polynomial/exterior basis monomials. This is not joint separation. -/
noncomputable section
open OddMath.SKM OddMath.SKM.ScalarChange OddMath.SKM.MixedCrossingLocalExamples

private def projection : (ℚ × ℚ) →+* ℚ := RingHom.fst ℚ ℚ

example (a : SYM.CoefficientIndex oddDatum) :
    symMap (D := oddDatum) projection (SYM.coefficientBasis oddDatum (ℚ × ℚ) a) =
      SYM.coefficientBasis oddDatum ℚ a :=
  symMap_coefficientBasis projection a

example : ¬ Function.Injective projection := by
  intro h
  have he := h (show projection (0, 1) = projection (0, 0) by rfl)
  have he' := congrArg Prod.snd he
  norm_num at he'

#print axioms OddMath.SKM.ScalarChange.symMap_coefficientBasis
