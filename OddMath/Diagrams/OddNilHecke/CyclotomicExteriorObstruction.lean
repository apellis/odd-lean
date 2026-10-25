import Mathlib.Tactic.NoncommRing

/-!
# Exterior coefficients and invertible cyclotomic constants

Supporting obstruction for the coefficient-separation problem in BE2 §8.
For the degree-two deformation `x² + xδ = b`, odd supercentrality and
`δ² = 0` force `2bδ = 0`. Thus a left-invertible `2b` kills `δ`.
This concerns this specified cyclotomic relation, not invertible odd dots
in arbitrary superalgebras. It is compatible with Ebert–Lauda–Vera,
arXiv:2203.14153v2, (3.24), with `d = -δ` and `χ₁ = -b`.
-/

namespace OddMath.OddNilHecke.CyclotomicExteriorObstruction

variable {A : Type*} [Ring A]

/-- The same obstruction holds with an arbitrary commuting polynomial in `x²`.
This covers the shape of every even-level ELV cyclotomic polynomial. -/
theorem twice_constant_mul_exterior_eq_zero_of_factor (x δ q b : A)
    (hδ : δ * δ = 0) (hanti : δ * x = -(x * δ))
    (hxq : q * x = x * q) (hδq : q * δ = δ * q)
    (hpoly : x * x * q + x * δ * q = b) (hcomm : x * b = b * x) :
    (2 : A) * b * δ = 0 := by
  have hc : x * (x * x * q + x * δ * q) =
      (x * x * q + x * δ * q) * x := by
    simpa only [hpoly] using hcomm
  have hz : x * x * δ * q + x * x * δ * q = 0 := by
    calc
      x * x * δ * q + x * x * δ * q =
          x * (x * x * q + x * δ * q) -
            (x * x * q + x * δ * q) * x := by
        have ha : δ * (x * q) = -(x * (δ * q)) := by
          rw [← mul_assoc, hanti, neg_mul, mul_assoc]
        noncomm_ring [hanti, hxq, ha]
      _ = 0 := sub_eq_zero.mpr hc
  calc
    (2 : A) * b * δ = x * x * δ * q + x * x * δ * q := by
      rw [← hpoly]
      simp only [mul_add, add_mul, mul_assoc]
      have hd : δ * (δ * q) = 0 := by rw [← mul_assoc, hδ, zero_mul]
      rw [hδq]
      simp only [hd, mul_zero, add_zero]
      noncomm_ring
    _ = 0 := hz

/-- The constant coefficient annihilates twice the exterior parameter. -/
theorem twice_constant_mul_exterior_eq_zero (x δ b : A)
    (hδ : δ * δ = 0) (hanti : δ * x = -(x * δ))
    (hpoly : x * x + x * δ = b) (hcomm : x * b = b * x) :
    (2 : A) * b * δ = 0 := by
  simpa only [mul_one] using
    twice_constant_mul_exterior_eq_zero_of_factor x δ 1 b hδ hanti
      (by simp) (by simp) (by simpa using hpoly) hcomm

/-- A left inverse for `2b` forces the exterior coefficient to vanish. -/
theorem exterior_eq_zero_of_leftInverse (x δ b a : A)
    (hδ : δ * δ = 0) (hanti : δ * x = -(x * δ))
    (hpoly : x * x + x * δ = b) (hcomm : x * b = b * x)
    (hinv : a * ((2 : A) * b) = 1) : δ = 0 := by
  calc
    δ = (a * ((2 : A) * b)) * δ := by rw [hinv, one_mul]
    _ = a * ((2 : A) * b * δ) := mul_assoc _ _ _
    _ = 0 := by
      rw [twice_constant_mul_exterior_eq_zero x δ b hδ hanti hpoly hcomm, mul_zero]

end OddMath.OddNilHecke.CyclotomicExteriorObstruction
