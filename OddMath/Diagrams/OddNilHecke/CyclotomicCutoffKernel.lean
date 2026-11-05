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

end OddMath.OddNilHecke.CyclotomicCutoffKernel
