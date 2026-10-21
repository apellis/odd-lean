import OddMath.Diagrams.EvenNilHecke.SmallRank
import Mathlib.Data.ZMod.Basic

/-!
# Polynomial consumers of the even nilHecke presentation

Concrete integer, rational and non-domain coefficient checks for the
polynomial action used before BE2 Lemma 11.1. Nonvanishing in arbitrary rank
is tested by the constant polynomial, not by an assumed faithful action.
-/

namespace OddMath.EvenNilHecke.PolynomialExamples
open MvPolynomial
open OddMath.EvenNilHecke.Polynomial

example (r : ℕ) : projectorAll r * projectorAll r = projectorAll r :=
  projectorAll_idempotent r
example : projectorAll 0 ≠ 0 := projectorAll_ne_zero 0
example : projectorAll 1 ≠ 0 := projectorAll_ne_zero 1
example : projectorAll 5 ≠ 0 := projectorAll_ne_zero 5

example : polynomialAction ℚ 1 (projector 1) 1 = 1 := polynomialAction_projector_one
example : polynomialAction (ZMod 4) 2 (projector 2) 1 = 1 := polynomialAction_projector_one

/-- A nonconstant two-strand test of the divided-difference formula. -/
theorem crossing_square_variable :
    polynomialAction ℤ 0 (crossing 0 0) (X (0 : Fin 2) ^ 2) = X 0 + X 1 := by
  rw [polynomialAction_crossing]
  apply ddiff_eq_of_mul (by decide)
  simp only [map_pow, rename_X]
  norm_num
  ring

/-- The spectator relation is realized over a non-domain coefficient ring. -/
theorem crossing_spectator :
    polynomialAction (ZMod 4) 1 (crossing 1 0) (X (2 : Fin 3) * X 0) = X 2 := by
  rw [polynomialAction_crossing]
  apply ddiff_eq_of_mul (by decide)
  simp only [map_mul, rename_X]
  norm_num [Equiv.swap_apply_def]
  ring

#print axioms crossing_square_variable
#print axioms crossing_spectator
#print axioms projectorAll_ne_zero

end OddMath.EvenNilHecke.PolynomialExamples
