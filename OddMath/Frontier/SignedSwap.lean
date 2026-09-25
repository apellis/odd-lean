import OddMath.DividedDifferences
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

/-!
# Signed swap on the actual rank-two skew-polynomial model

Source: EKL, arXiv:1111.1320v1, §2.1.1, (2.1)–(2.2), p.3.
The inherited `symm1` includes both generator negations and the Koszul sign
needed to restore increasing-index order. No degree bound is imposed.
This proves the ring-action laws in the finite-support integer model, not a
quotient/model equivalence or any divided-difference relation.
-/

namespace OddMath.Frontier.SignedSwap

open OddMath.SkewPolynomial OddMath.DividedDifferences

/-- The unique crossing in rank two has weight `a 1 * b 0`. -/
theorem crossingCount_two (a b : Fin 2 → ℕ) :
    OddMath.crossingCount a b = a 1 * b 0 := by
  simp [OddMath.crossingCount, Finset.sum_filter, Fin.sum_univ_two]

/-- Swapping coordinates preserves pointwise exponent addition. -/
theorem swapExp_add (a b : Fin 2 → ℕ) :
    swapExp (a + b) = swapExp a + swapExp b := rfl

/-- Symbolic compatibility of the reorder sign and signed transposition. -/
theorem swapSign_product (a b : Fin 2 → ℕ) :
    OddMath.skewSign a b * swapSign (a + b) =
      swapSign a * swapSign b * OddMath.skewSign (swapExp a) (swapExp b) := by
  simp only [OddMath.skewSign, crossingCount_two, swapSign,
    Pi.add_apply, swapExp_apply_zero, swapExp_apply_one, ← pow_add]
  have he : a 1 * b 0 + (a 0 + b 0 + (a 1 + b 1) + (a 0 + b 0) * (a 1 + b 1)) =
      (a 0 + a 1 + a 0 * a 1 + (b 0 + b 1 + b 0 * b 1) + a 0 * b 1)
        + 2 * (a 1 * b 0) := by ring
  rw [he, pow_add, pow_mul]
  norm_num

/-- Multiplicativity on arbitrary monomials, including arbitrary coefficients. -/
theorem symm1_mul_monomial (a b : Fin 2 → ℕ) (r s : ℤ) :
    symm1 (mul (monomial a r) (monomial b s)) =
      mul (symm1 (monomial a r)) (symm1 (monomial b s)) := by
  simp only [mul_monomial, symm1_monomial, swapExp_add]
  congr 1
  calc
    r * s * OddMath.skewSign a b * swapSign (a + b) =
        (r * s) * (OddMath.skewSign a b * swapSign (a + b)) := by ring
    _ = (r * s) * (swapSign a * swapSign b *
        OddMath.skewSign (swapExp a) (swapExp b)) := by rw [swapSign_product]
    _ = r * swapSign a * (s * swapSign b) *
        OddMath.skewSign (swapExp a) (swapExp b) := by ring

/-- Signed swap preserves multiplication of arbitrary finite-support polynomials. -/
theorem symm1_mul (f g : SkewPolynomial 2) :
    symm1 (mul f g) = mul (symm1 f) (symm1 g) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [zero_mul, symm1_zero]
  | add f₁ f₂ ih₁ ih₂ =>
      simp only [add_mul, symm1_add, ih₁, ih₂]
  | single a r =>
      induction g using Finsupp.induction_linear with
      | zero => simp only [mul_zero, symm1_zero]
      | add g₁ g₂ ih₁ ih₂ =>
          simp only [mul_add, symm1_add, ih₁, ih₂]
      | single b s => exact symm1_mul_monomial a b r s

/-- The signed swap squares to the identity on every polynomial. -/
theorem symm1_involute (f : SkewPolynomial 2) : symm1 (symm1 f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [symm1_zero]
  | add f g ihf ihg => simp only [symm1_add, ihf, ihg]
  | single a r => exact symm1_involute_monomial a r

/-- Functional interface for the involution law. -/
theorem symm1_involutive : Function.Involutive symm1 := symm1_involute

end OddMath.Frontier.SignedSwap
