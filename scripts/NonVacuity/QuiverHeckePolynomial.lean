import OddMath

/-! Non-vacuity for the mixed polynomial coefficient algebra, HW Proposition 4.5 prerequisite. -/
noncomputable section
namespace OddMath.QuiverHecke.NonVacuityPolynomial
open OddMath.QuiverHecke.Polynomial PolynomialExamples

example : Polynomial ℚ 3 mixedParity := X mixedParity 0

example : X (R := ℚ) mixedParity 0 * X mixedParity 1 =
    -(X mixedParity 1 * X mixedParity 0) := by
  simpa [mixedParity] using X_mul_X_swap (R := ℚ) mixedParity 0 1 (by decide)

example : X (R := ℚ) mixedParity 0 * X mixedParity 2 =
    X mixedParity 2 * X mixedParity 0 := by
  simpa [mixedParity] using X_mul_X_swap (R := ℚ) mixedParity 0 2 (by decide)

example : X (R := ℚ) mixedParity 0 ^ 2 ≠ 0 := X_sq_ne_zero mixedParity 0

example : LinearIndependent ℚ (fun a => monomial (R := ℚ) mixedParity a 1) :=
  (monomialBasis mixedParity).linearIndependent

example : Function.Injective (leftRegular (R := ℚ) mixedParity) :=
  leftRegular_injective mixedParity

example (f : Polynomial ℚ 3 mixedParity) : Commute (X mixedParity 0 ^ 2) f :=
  X_sq_commute mixedParity 0 f

example : wordDot (R := ℚ) Examples.datum [(), ()] 0 ^ 2 ≠ 0 :=
  wordDot_sq_ne_zero Examples.datum [(), ()] 0

#print axioms monomialBasis
#print axioms X_mul_X_swap
#print axioms X_sq_commute
#print axioms wordDot_mul_swap

end OddMath.QuiverHecke.NonVacuityPolynomial
