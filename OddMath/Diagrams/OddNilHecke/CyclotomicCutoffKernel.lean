import Mathlib.Tactic.NoncommRing

/-!
# A genuine finite-cutoff PBW relation

For the exterior deformation `f_N = x^N + x^(N-1)δ`, the nilHecke relations
force `(∂f_N)τ = 0`. This is an obstruction at the finite cutoff, not an
obstruction to eventual bounded-degree independence as the cutoff grows.
-/

namespace OddMath.OddNilHecke.CyclotomicCutoffKernel

variable {A : Type*} [Ring A]

/-- The left divided-difference polynomial of `x^n`. -/
def dividedPower (x y : A) : ℕ → A
  | 0 => 0
  | n + 1 => x ^ n - y * dividedPower x y n

/-- Move a crossing through a power of the first dot. -/
theorem crossing_power (x y τ : A) (hslide : τ * x + y * τ = 1) (n : ℕ) :
    τ * x ^ n = dividedPower x y n + (-y) ^ n * τ := by
  induction n with
  | zero => simp [dividedPower]
  | succ n ih =>
    have ht : τ * x = 1 - y * τ := eq_sub_of_add_eq hslide
    rw [pow_succ', ← mul_assoc, ht, sub_mul, one_mul, mul_assoc, ih]
    rw [dividedPower, pow_succ']
    noncomm_ring

/-- The exterior cyclotomic relation supplies a nonzero formal PBW relation
one coefficient/dot degree below the cutoff. No evenness assumption is needed
for this algebraic identity. -/
theorem cutoff_kernel (x y τ δ : A) (n : ℕ)
    (hslide : τ * x + y * τ = 1) (hτ : τ * τ = 0)
    (hanti : τ * δ = -(δ * τ))
    (hcutoff : x ^ (n + 1) + x ^ n * δ = 0) :
    (dividedPower x y (n + 1) + dividedPower x y n * δ) * τ = 0 := by
  have hδτ : τ * (δ * τ) = 0 := by
    rw [← mul_assoc, hanti, neg_mul, mul_assoc, hτ, mul_zero, neg_zero]
  have h := congrArg (fun a : A => τ * a * τ) hcutoff
  simp only [mul_add, add_mul, mul_zero] at h
  rw [crossing_power x y τ hslide (n + 1)] at h
  rw [← mul_assoc τ (x ^ n) δ, crossing_power x y τ hslide n] at h
  simp only [add_mul, mul_assoc, hτ, hδτ, mul_zero, add_zero] at h
  simpa only [add_mul, mul_assoc, zero_mul] using h

end OddMath.OddNilHecke.CyclotomicCutoffKernel
