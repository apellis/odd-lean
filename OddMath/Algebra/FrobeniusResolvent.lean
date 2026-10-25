import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Resolvent moments for a monic Frobenius algebra

Supports the highest-probe-vacuum calculation in
`docs/Nondegeneracy/SpectralCompensation.md`. A monic relation and the
coefficient-of-the-highest-power trace determine all low resolvent moments.
No roots, separability, or diagonalization are assumed.
-/

namespace OddMath.FrobeniusResolvent

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

private theorem step (τ : A →ₗ[R] R) (y r : A) (z : R)
    (hr : (algebraMap R A z - y) * r = 1) (k : ℕ) :
    τ (y ^ (k + 1) * r) = z * τ (y ^ k * r) - τ (y ^ k) := by
  have he : y ^ (k + 1) * r = z • (y ^ k * r) - y ^ k := by
    have h := congrArg (fun a : A => y ^ k * a) hr
    simp only [Algebra.smul_def]
    rw [pow_succ]
    linear_combination -h
  rw [he, map_sub, map_smul]
  rfl

/-- Below the top degree, every resolvent moment is a power of the spectral
parameter times the zeroth moment. The next moment has exactly one correction. -/
theorem moments (τ : A →ₗ[R] R) (y r : A) (z : R) (m : ℕ)
    (hm : 0 < m) (hr : (algebraMap R A z - y) * r = 1)
    (hτ : ∀ k < m, τ (y ^ k) = if k + 1 = m then 1 else 0)
    (k : ℕ) (hk : k ≤ m) :
    τ (y ^ k * r) = z ^ k * τ r - if k = m then 1 else 0 := by
  induction k with
  | zero => simp [Ne.symm (Nat.ne_of_gt hm)]
  | succ k ih =>
    have hkm : k < m := by omega
    rw [step τ y r z hr k, ih (by omega), hτ k hkm]
    simp only [Nat.ne_of_lt hkm, ite_false, sub_zero]
    rw [pow_succ]
    ring

/-- The monic characteristic polynomial times the zeroth resolvent trace is
one. This works over an arbitrary commutative base ring. -/
theorem characteristic_mul_trace (τ : A →ₗ[R] R) (y r : A) (z : R)
    (m : ℕ) (hm : 0 < m) (c : Fin m → R)
    (hy : y ^ m + ∑ k : Fin m, c k • y ^ (k : ℕ) = 0)
    (hr : (algebraMap R A z - y) * r = 1)
    (hτ : ∀ k < m, τ (y ^ k) = if k + 1 = m then 1 else 0) :
    (z ^ m + ∑ k : Fin m, c k * z ^ (k : ℕ)) * τ r = 1 := by
  have he := congrArg (fun a : A => τ (a * r)) hy
  simp only [add_mul, Finset.sum_mul, smul_mul_assoc, map_add, map_sum,
    map_smul, smul_eq_mul, zero_mul, map_zero] at he
  rw [moments τ y r z m hm hr hτ m le_rfl] at he
  simp only [ite_true] at he
  have low (k : Fin m) : τ (y ^ (k : ℕ) * r) = z ^ (k : ℕ) * τ r := by
    rw [moments τ y r z m hm hr hτ k (Nat.le_of_lt k.isLt)]
    simp [Nat.ne_of_lt k.isLt]
  simp_rw [low] at he
  rw [add_mul, Finset.sum_mul]
  simp_rw [mul_assoc]
  linear_combination he

/-- All low moments satisfy the same characteristic denominator identity. -/
theorem characteristic_mul_moment (τ : A →ₗ[R] R) (y r : A) (z : R)
    (m : ℕ) (hm : 0 < m) (c : Fin m → R)
    (hy : y ^ m + ∑ k : Fin m, c k • y ^ (k : ℕ) = 0)
    (hr : (algebraMap R A z - y) * r = 1)
    (hτ : ∀ k < m, τ (y ^ k) = if k + 1 = m then 1 else 0)
    (j : ℕ) (hj : j < m) :
    (z ^ m + ∑ k : Fin m, c k * z ^ (k : ℕ)) * τ (y ^ j * r) = z ^ j := by
  rw [moments τ y r z m hm hr hτ j (Nat.le_of_lt hj)]
  simp only [Nat.ne_of_lt hj, ite_false, sub_zero]
  rw [mul_left_comm, characteristic_mul_trace τ y r z m hm c hy hr hτ, mul_one]

end OddMath.FrobeniusResolvent
