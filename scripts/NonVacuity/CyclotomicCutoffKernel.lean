import OddMath.Diagrams.OddNilHecke.CyclotomicCutoffKernel
import OddMath.Diagrams.OddNilHecke.ExteriorDeformation

open OddMath.OddNilHecke
open ExteriorDeformation

-- The first finite-cutoff relation occurs with a genuinely nonzero exterior scalar.
example : exterior dualParameter ≠ 0 ∧
    (firstDot dualParameter - secondDot dualParameter + exterior dualParameter) *
      crossing = 0 := by
  refine ⟨dualNumber_model.1, ?_⟩
  have hs : dualParameter * dualParameter = 0 := TrivSqZeroExt.inr_mul_inr ℚ 1 1
  have hn := nilHecke_relations dualParameter
  have hc : firstDot dualParameter ^ (1 + 1) +
      firstDot dualParameter ^ 1 * exterior dualParameter = 0 := by
    simpa only [Nat.reduceAdd, pow_one, pow_two] using dualNumber_model.2.2
  have ha : crossing * exterior dualParameter = -(exterior dualParameter * crossing) :=
    eq_neg_of_add_eq_zero_right (exterior_anticommutes dualParameter hs).2.2
  have h := CyclotomicCutoffKernel.cutoff_kernel
    (firstDot dualParameter) (secondDot dualParameter) crossing (exterior dualParameter)
    1 hn.2.2.1 hn.1 ha hc
  simpa [CyclotomicCutoffKernel.dividedPower] using h

#print axioms CyclotomicCutoffKernel.crossing_power
#print axioms CyclotomicCutoffKernel.cutoff_kernel
