/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.CoupledBubbleEvaluation

/-! # Triangular recovery of reservoir bubble coefficients

Algebraic part of C1 in `docs/Nondegeneracy/GeneralRoute.md`. A categorical
bubble convolution is still a hypothesis. The inverse is finite in every
coefficient, works over rings with zero divisors, and does not assert that a
substitution preserves a finite cyclotomic ideal. Apply it separately to each
colour's even series; all odd coefficients must remain in the same reservoir.
-/
namespace OddMath.SKM

/-- Ordered multiplication of coefficient series. -/
def reservoirConvolution {R : Type*} [Ring R] (A P : ℕ → R) (n : ℕ) : R :=
  ∑ r ∈ Finset.range (n + 1), A (n - r) * P r

/-- Recover one coefficient at a time by subtracting the already known lower
coefficients. No infinite sum and no division by an exterior element is used. -/
def reservoirDeconvolution {R : Type*} [Ring R] (C P : ℕ → R) (n : ℕ) : R :=
  C n - ∑ r : Fin n, reservoirDeconvolution C P (n - (r.val + 1)) * P (r.val + 1)
termination_by n
decreasing_by have := r.isLt; omega

/-- The finite triangular inverse, including the constant coefficient. -/
theorem reservoirDeconvolution_convolution {R : Type*} [Ring R]
    (A P : ℕ → R) (hP : P 0 = 1) (n : ℕ) :
    reservoirDeconvolution (reservoirConvolution A P) P n = A n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [reservoirDeconvolution]
    have hs : (∑ r : Fin n,
        reservoirDeconvolution (reservoirConvolution A P) P (n - (r.val + 1)) * P (r.val + 1)) =
        ∑ r ∈ Finset.range n, A (n - (r + 1)) * P (r + 1) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro r _
      rw [ih (n - (r.val + 1)) (by have := r.isLt; omega)]
    rw [hs, reservoirConvolution, Finset.sum_range_succ', Nat.sub_zero, hP, mul_one]
    exact add_sub_cancel_left _ _

/-- Conversely, reconvolution reconstructs every series. This is a genuine
triangular inverse, not merely injectivity of multiplication by the probe. -/
theorem reservoirConvolution_deconvolution {R : Type*} [Ring R]
    (C P : ℕ → R) (hP : P 0 = 1) (n : ℕ) :
    reservoirConvolution (reservoirDeconvolution C P) P n = C n := by
  rw [reservoirConvolution, Finset.sum_range_succ', Nat.sub_zero, hP, mul_one]
  conv_lhs => rhs; rw [reservoirDeconvolution]
  rw [← Fin.sum_univ_eq_sum_range]
  abel

/-- Only the coefficients through the requested degree are used in recovery. -/
theorem reservoirDeconvolution_eq_upto {R : Type*} [Ring R]
    (C C' P : ℕ → R) (N : ℕ) (h : ∀ n ≤ N, C n = C' n) :
    ∀ n ≤ N, reservoirDeconvolution C P n = reservoirDeconvolution C' P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rw [reservoirDeconvolution, reservoirDeconvolution, h n hn]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [ih (n - (r.val + 1)) (by have := r.isLt; omega) (by omega)]

/-- A proposed normalized categorical series determines every bounded reservoir
coefficient once its ordered probe-convolution formula has been proved. -/
theorem reservoir_coefficients_recovered {R : Type*} [Ring R]
    (C A P : ℕ → R) (N : ℕ) (hP : P 0 = 1)
    (formula : ∀ n ≤ N, C n = reservoirConvolution A P n) :
    ∀ n ≤ N, reservoirDeconvolution C P n = A n := by
  intro n hn
  rw [reservoirDeconvolution_eq_upto C (reservoirConvolution A P) P N formula n hn,
    reservoirDeconvolution_convolution A P hP]

/-- A unit normalization of an odd coefficient is harmless. This uses only
left multiplication by its inverse, not a localization of the coefficient ring. -/
theorem reservoir_exterior_recovered {R : Type*} [Ring R]
    (u : Rˣ) (delta b : R) (formula : b = (u : R) * delta) :
    (↑(u⁻¹) : R) * b = delta := by
  rw [formula, ← mul_assoc, Units.inv_mul, one_mul]

end OddMath.SKM
