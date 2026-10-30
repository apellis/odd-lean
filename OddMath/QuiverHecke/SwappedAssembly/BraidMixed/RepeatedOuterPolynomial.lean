/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic

/-! # Ordered repeated-outer polynomial corrections

Finite polynomial identities supporting the repeated-outer terms of `CrossBraid`
(`OddMath.QuiverHecke.SwappedAssembly.Braid`). Multiplication is kept in the displayed order;
in endomorphism algebras this is reverse chronological composition. The odd
identity uses even outer exponents and anticommutation, without inverting Q
or a crossing. The middle-factor corollaries explicitly require commutation
with the right outer dot; they do not assert this for arbitrary odd middle dots.
-/

open Finset
namespace OddMath.QuiverHecke.SwappedAssembly.RepeatedOuterPolynomial
variable {R : Type*} [Ring R]

lemma sum_pairs (f : ℕ → R) (n : ℕ) :
    ∑ a ∈ range (2 * n), f a = ∑ b ∈ range n, (f (2*b) + f (2*b+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n+1) = (2*n+1)+1 by omega, sum_range_succ, sum_range_succ,
      ih, sum_range_succ]
    simp only [add_assoc]

lemma square_commute (x z : R) (h : x*z = -(z*x)) : Commute (x^2) z := by
  show x^2*z = z*x^2
  rw [pow_two]
  calc
    x*x*z = x*(x*z) := mul_assoc _ _ _
    _ = -(x*(z*x)) := by rw [h, mul_neg]
    _ = -((x*z)*x) := by rw [mul_assoc]
    _ = z*(x*x) := by rw [h, neg_mul, neg_neg, mul_assoc]

lemma ordered_telescoping (x z : R) (h : Commute x z) (n : ℕ) :
    (x-z) * (∑ a ∈ range n, x^(n-1-a)*z^a) = x^n-z^n := by
  have hs : (∑ a ∈ range n, x^(n-1-a)*z^a) =
      ∑ a ∈ range n, x^a*z^(n-1-a) := by
    rw [← sum_range_reflect (fun a => x^a*z^(n-1-a)) n]
    apply sum_congr rfl
    intro a ha
    have ha' := mem_range.mp ha
    rw [show n-1-(n-1-a) = a by omega]
  rw [hs]
  exact h.mul_geom_sum₂ n

lemma alternating_pairs (x z : R) (h : x*z = -(z*x)) (n : ℕ) :
    (x-z) * (∑ a ∈ range n, (x^2)^(n-1-a)*(z^2)^a) =
      ∑ a ∈ range (2*n), (-1:R)^a * (x^(2*n-1-a)*z^a) := by
  rw [sum_pairs, mul_sum]
  apply sum_congr rfl
  intro a ha
  have ha' := mem_range.mp ha
  have hx := (square_commute x z h).pow_left (n-1-a)
  have he : 2*n-1-2*a = 2*(n-1-a)+1 := by omega
  have ho : 2*n-1-(2*a+1) = 2*(n-1-a) := by omega
  rw [he, ho]
  simp only [pow_mul, pow_add, pow_one, neg_one_sq, one_pow, one_mul,
    mul_neg, mul_one, neg_mul, sub_mul]
  simp only [← pow_mul]
  rw [← pow_mul] at hx
  rw [← mul_assoc, ← mul_assoc, hx.symm.eq,
    (Commute.self_pow x (2*(n-1-a))).eq]
  simp only [mul_assoc, sub_eq_add_neg]
  rw [(Commute.self_pow z (2*a)).eq]

/-- An anticommuting pair admits the ordered signed even-degree correction.
No commutation or inverse assumption on `A` is required beyond the displayed equation. -/
theorem odd_correction (A x z : R) (h : x*z = -(z*x))
    (hA : A*(x*x-z*z) = x-z) (n : ℕ) :
    A*(x^(2*n)-z^(2*n)) =
      ∑ a ∈ range (2*n), (-1:R)^a * (x^(2*n-1-a)*z^a) := by
  have hc : Commute (x^2) (z^2) := (square_commute x z h).pow_right 2
  rw [pow_mul x 2 n, pow_mul z 2 n, ← ordered_telescoping _ _ hc,
    ← mul_assoc, show A*(x^2-z^2) = x-z by simpa only [pow_two] using hA]
  exact alternating_pairs x z h n
/-- The even correction needs only commuting dots and a left inverse of their difference. -/
theorem even_correction (A x z : R) (h : Commute x z)
    (hA : A * (x-z) = 1) (n : ℕ) :
    A * (x^n-z^n) = ∑ a ∈ range n, x^(n-1-a)*z^a := by
  rw [← ordered_telescoping x z h n, ← mul_assoc, hA, one_mul]

variable {k : Type*} [CommRing k] [Algebra k R]

/-- The signed ordered odd correction, over an arbitrary commutative scalar ring. -/
theorem odd_correction_smul (A x z : R) (h : x*z = -(z*x))
    (hA : A*(x*x-z*z) = x-z) (n : ℕ) :
    A*(x^(2*n)-z^(2*n)) =
      ∑ a ∈ range (2*n), (-1:k)^a • (x^(2*n-1-a)*z^a) := by
  simpa only [Algebra.smul_def, map_pow, map_neg, map_one] using
    odd_correction A x z h hA n

/-- A middle monomial can be inserted without changing the chronological order.
Only its commutation with the right outer dot is needed. -/
theorem odd_correction_middle (A x z m : R) (h : x*z = -(z*x))
    (hA : A*(x*x-z*z) = x-z) (hm : Commute z m) (n c : ℕ) :
    A*(x^(2*n)-z^(2*n))*m^c =
      ∑ a ∈ range (2*n), (-1:k)^a • (x^(2*n-1-a)*m^c*z^a) := by
  rw [odd_correction_smul (k := k) A x z h hA, sum_mul]
  apply sum_congr rfl
  intro a _
  rw [smul_mul_assoc, mul_assoc, (hm.pow_pow a c).eq, ← mul_assoc]

/-- Finite linear combinations of even outer monomials, with the middle factor
kept between the ordered outer powers on the correction side. -/
theorem odd_polynomial_correction {ι : Type*} (s : Finset ι)
    (w : ι → k) (n c : ι → ℕ) (A x z m : R)
    (h : x*z = -(z*x)) (hA : A*(x*x-z*z) = x-z) (hm : Commute z m) :
    A * (∑ t ∈ s, w t • ((x^(2*n t)-z^(2*n t))*m^(c t))) =
      ∑ t ∈ s, w t • (∑ a ∈ range (2*n t),
        (-1:k)^a • (x^(2*n t-1-a)*m^(c t)*z^a)) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro t _
  rw [mul_smul_comm, ← mul_assoc, odd_correction_middle (k := k) A x z m h hA hm]

end OddMath.QuiverHecke.SwappedAssembly.RepeatedOuterPolynomial
