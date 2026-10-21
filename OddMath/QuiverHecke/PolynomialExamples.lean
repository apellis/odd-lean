/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.PolynomialWord
import OddMath.QuiverHecke.Examples

/-! Mixed and odd coefficient-algebra consumers for HW Proposition 4.5. -/
noncomputable section
namespace OddMath.QuiverHecke.PolynomialExamples
open OddMath.QuiverHecke.Polynomial

/-- Two odd positions and one even position in the same coefficient algebra. -/
def mixedParity : Fin 3 → Bool := ![true, true, false]

example : X (R := ℚ) mixedParity 0 * X mixedParity 1 =
    -(X mixedParity 1 * X mixedParity 0) := by
  simpa [mixedParity] using X_mul_X_swap (R := ℚ) mixedParity 0 1 (by decide)

example : X (R := ℚ) mixedParity 0 * X mixedParity 2 =
    X mixedParity 2 * X mixedParity 0 := by
  simpa [mixedParity] using X_mul_X_swap (R := ℚ) mixedParity 0 2 (by decide)

example : X (R := ℚ) mixedParity 0 ^ 2 ≠ 0 := X_sq_ne_zero mixedParity 0

example (f : Polynomial ℚ 3 mixedParity) : Commute (X mixedParity 0 ^ 2) f :=
  X_sq_commute mixedParity 0 f

example : LinearIndependent ℚ (fun a => monomial (R := ℚ) mixedParity a 1) :=
  (monomialBasis mixedParity).linearIndependent

example : Function.Injective (leftRegular (R := ℚ) mixedParity) :=
  leftRegular_injective mixedParity

example (n : ℕ) (r : Fin n) :
    X (R := ℚ) (fun _ : Fin n => true) r ^ 2 ≠ 0 := X_sq_ne_zero _ r

example : wordDot (R := ℚ) Examples.datum [(), ()] 0 *
    wordDot Examples.datum [(), ()] 1 =
      -(wordDot Examples.datum [(), ()] 1 * wordDot Examples.datum [(), ()] 0) := by
  simpa [SKM.zsign, Examples.datum] using
    wordDot_mul_swap (R := ℚ) Examples.datum [(), ()] 0 1 (by decide)

example : wordDot (R := ℚ) Examples.datum [(), ()] 0 ^ 2 ≠ 0 :=
  wordDot_sq_ne_zero Examples.datum [(), ()] 0

#print axioms monomial_mul
#print axioms monomialBasis
#print axioms X_mul_X_swap
#print axioms X_sq_ne_zero
#print axioms X_sq_commute
#print axioms leftRegular_injective
#print axioms wordDot_mul_swap
#print axioms wordDot_sq_ne_zero

end OddMath.QuiverHecke.PolynomialExamples
