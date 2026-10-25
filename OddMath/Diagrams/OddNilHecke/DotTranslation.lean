/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.NoncommRing

/-!
# Translation of an odd dot by an independent exterior coefficient

Local algebra supporting the coefficient-detection route to Brundan–Ellis
arXiv:1701.04133v2, Section 8. These identities do not construct a full action.
-/
namespace OddMath.OddNilHecke.DotTranslation
variable {R : Type*} [Ring R]

theorem square (x d : R) (hd : d * d = 0) (hx : x * d + d * x = 0) :
    (x + d) ^ 2 = x ^ 2 := by
  have hdx : d * x = -(x * d) := eq_neg_of_add_eq_zero_right hx
  noncomm_ring [hd, hdx]

theorem even_pow (x d : R) (hd : d * d = 0) (hx : x * d + d * x = 0)
    (m : ℕ) : (x + d) ^ (2 * m) = x ^ (2 * m) := by
  rw [pow_mul, pow_mul, square x d hd hx]

theorem odd_pow (x d : R) (hd : d * d = 0) (hx : x * d + d * x = 0)
    (m : ℕ) : (x + d) ^ (2 * m + 1) = x ^ (2 * m + 1) + x ^ (2 * m) * d := by
  rw [pow_succ, even_pow x d hd hx, mul_add, ← pow_succ]

/-- The odd nilHecke dot-slide survives simultaneous exterior translation. -/
theorem slide (x y τ d : R) (hτ : τ * d + d * τ = 0)
    (h : τ * x + y * τ = 1) :
    τ * (x + d) + (y + d) * τ = 1 := by
  have hdτ : d * τ = -(τ * d) := eq_neg_of_add_eq_zero_right hτ
  have hτx : τ * x = 1 - y * τ := eq_sub_of_add_eq h
  noncomm_ring [hdτ, hτx]

end OddMath.OddNilHecke.DotTranslation
