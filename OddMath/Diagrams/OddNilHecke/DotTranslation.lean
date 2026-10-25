/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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

private theorem sum_range_pairs {A : Type*} [AddCommMonoid A] (f : ℕ → A) (m : ℕ) :
    ∑ s ∈ Finset.range (2 * m), f s =
      ∑ r ∈ Finset.range m, (f (2 * r) + f (2 * r + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simpa [Nat.mul_succ, Finset.sum_range_succ, add_assoc] using
      congrArg (fun a => a + f (2 * m) + f (2 * m + 1)) ih

/-- The alternating divided difference appearing in a repeated-odd-colour
braid correction, with an even middle coefficient/operator `a`. -/
def braidPolynomial (x a z : R) (m : ℕ) : R :=
  ∑ s ∈ Finset.range (2 * m), (-1) ^ s * (x ^ (2 * m - 1 - s) * a * z ^ s)

/-- Pairing adjacent summands exposes only squared outer dots and
`x*a-a*z`. No commutation between the outer dots is needed. -/
theorem braidPolynomial_paired (x a z : R) (m : ℕ) :
    braidPolynomial x a z m =
      ∑ r ∈ Finset.range m,
        x ^ (2 * (m - 1 - r)) * (x * a - a * z) * z ^ (2 * r) := by
  rw [braidPolynomial, sum_range_pairs]
  apply Finset.sum_congr rfl
  intro r hr
  have hrm := Finset.mem_range.mp hr
  have he : 2 * m - 1 - 2 * r = 2 * (m - 1 - r) + 1 := by omega
  have ho : 2 * m - 1 - (2 * r + 1) = 2 * (m - 1 - r) := by omega
  have hs : (-1 : R) ^ (2 * r) = 1 := by
    rw [pow_mul]
    rw [show (-1 : R) ^ 2 = 1 by noncomm_ring]
    simp
  rw [he, ho, pow_succ (-1 : R), hs, one_mul, one_mul, neg_one_mul,
    pow_succ x, pow_succ' z]
  noncomm_ring

/-- Simultaneous translation preserves the exact alternating correction.
The middle operator must commute with the exterior coefficient. -/
theorem braidPolynomial_translate (x a z d : R) (m : ℕ)
    (hd : d * d = 0) (hx : x * d + d * x = 0)
    (hz : z * d + d * z = 0) (ha : d * a = a * d) :
    braidPolynomial (x + d) a (z + d) m = braidPolynomial x a z m := by
  rw [braidPolynomial_paired, braidPolynomial_paired]
  apply Finset.sum_congr rfl
  intro r _
  rw [even_pow x d hd hx, even_pow z d hd hz]
  have hc : (x + d) * a - a * (z + d) = x * a - a * z := by
    noncomm_ring [ha]
  rw [hc]

end OddMath.OddNilHecke.DotTranslation
