import OddMath.SkewPolynomial

/-! Hand-derived fixtures; see the development notes for derivations before implementation. -/
namespace OddMath.SkewPolynomial.Tests

example : mul (monomial (0 : Fin 0 → ℕ) 2) (monomial 0 (-3)) =
    monomial 0 (-6) := by
  rw [mul_monomial]
  congr 1

example : mul (monomial ![1] 1) (monomial ![1] 1) = monomial ![2] 1 := by
  rw [mul_monomial]
  congr 1; decide

example : mul (monomial ![2] 1) (monomial ![2] 1) = monomial ![4] 1 := by
  rw [mul_monomial]
  congr 1; decide

example : mul (monomial ![1, 0] 1) (monomial ![0, 1] 1) =
    monomial ![1, 1] 1 := by
  rw [mul_monomial]
  congr 1; decide

example : mul (monomial ![0, 1] 1) (monomial ![1, 0] 1) =
    monomial ![1, 1] (-1) := by
  rw [mul_monomial]
  congr 1; decide

example : mul (mul (monomial ![0, 1] 1) (monomial ![1, 0] 1))
    (monomial ![1, 0] 1) = monomial ![2, 1] 1 := by
  rw [mul_monomial, mul_monomial]
  congr 1; decide

example : mul (monomial ![0, 2] 1) (monomial ![2, 0] 1) =
    monomial ![2, 2] 1 := by
  rw [mul_monomial]
  congr 1; decide

example : (mul (monomial ![1, 0] 1 + monomial ![0, 1] 1)
    (monomial ![1, 0] 1 + monomial ![0, 1] 1)) ![1, 1] = 0 := by
  rw [add_mul, mul_add, mul_add]
  simp only [mul_monomial, Finsupp.add_apply, monomial, Finsupp.single_apply]
  decide

example : mul (generator (0 : Fin 1)) (generator 0) ≠ 0 :=
  generator_square_ne_zero 0

example : (mul (generator (0 : Fin 2)) (generator 1)) ![1, 1] = 1 :=
  ordered_rank_two_coordinate

end OddMath.SkewPolynomial.Tests
