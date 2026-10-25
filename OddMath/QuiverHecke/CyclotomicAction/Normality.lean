import OddMath.QuiverHecke.CyclotomicAction.SignedMultipliers

/-!
# First-dot normality for the deformed cyclotomic polynomial

These are ring identities for the even-cutoff polynomial
`χ + x² q - x d q`, with `d²=0`, `dx=-xd`, and `χd=0`.
The normalizer shifts the dot by `-2d`; its inverse shifts by `+2d`.
The coefficient `q` stands for a polynomial in the central square variable.

The identities do not construct the all-content balanced bimodules or prove
that their quotient kernel is the cyclotomic relation span.
-/
namespace OddMath.QuiverHecke.CyclotomicAction

variable {A : Type*} [Ring A]

/-- Normality, with the top-coefficient annihilation condition explicit. -/
theorem evenCutoff_normality (x d χ q : A)
    (hdx : d * x = -(x * d)) (hd : d * d = 0)
    (hqx : q * x = x * q) (hqd : q * d = d * q)
    (hxχ : x * χ = χ * x) (hχd : χ * d = 0) :
    x * (χ + x * x * q - x * d * q) =
      (χ + x * x * q - x * d * q) * (x - 2 * d) := by
  linear_combination (norm := noncomm_ring)
    hxχ - x * x * hqx + x * d * hqx + x * hdx * q +
      2 * x * x * hqd + 2 * hχd - 2 * x * d * hqd - 2 * x * hd * q

/-- The domain twist for right multiplication is the inverse normalizer. -/
theorem evenCutoff_inverse_balance (x d χ q : A)
    (hdx : d * x = -(x * d)) (hd : d * d = 0)
    (hqx : q * x = x * q)
    (hxχ : x * χ = χ * x) (hdχ : d * χ = 0) :
    (x + 2 * d) * (χ + x * x * q - x * d * q) =
      (χ + x * x * q - x * d * q) * x := by
  linear_combination (norm := noncomm_ring)
    hxχ - x * x * hqx + x * d * hqx - x * hdx * q +
      2 * hdx * x * q + 2 * hdχ + 2 * x * hd * q - 2 * hdx * d * q

/-- Exterior translation fixes the square coordinate. -/
theorem normalizer_square (x d : A) (hdx : d * x = -(x * d)) (hd : d * d = 0) :
    (x - 2 * d) * (x - 2 * d) = x * x := by
  linear_combination (norm := noncomm_ring) -2 * hdx + 4 * hd

/-- The normalizer fixes the deformation term as well. -/
theorem normalizer_xd (x d : A) (hd : d * d = 0) :
    (x - 2 * d) * d = x * d := by
  linear_combination (norm := noncomm_ring) -2 * hd

/-- The exterior part of the polynomial has square zero. -/
theorem deformation_square_zero (x d q : A)
    (hdx : d * x = -(x * d)) (hd : d * d = 0)
    (hqx : q * x = x * q) (hqd : q * d = d * q) :
    (x * d * q) * (x * d * q) = 0 := by
  linear_combination (norm := noncomm_ring)
    x * d * hqx * d * q + x * hdx * q * d * q -
      x * x * d * hqd * q - x * x * hd * q * q

/-- The conjugate gives the central-square annihilator without projectivity. -/
theorem evenCutoff_conjugate (C x d q : A)
    (hdx : d * x = -(x * d)) (hd : d * d = 0)
    (hqx : q * x = x * q) (hqd : q * d = d * q)
    (hC : C * (x * d * q) = (x * d * q) * C) :
    (C + x * d * q) * (C - x * d * q) = C * C := by
  have hn := deformation_square_zero x d q hdx hd hqx hqd
  linear_combination (norm := noncomm_ring) -hC - hn

/-- At odd cutoff the coefficient parity involution is part of the normalizer. -/
theorem oddCutoff_normality (x d C : A)
    (hdx : d * x = -(x * d)) (hd : d * d = 0)
    (hCx : C * x = x * C) (hCd : C * d = d * C) :
    x * ((x - d) * C) = ((x - d) * C) * (x - 2 * d) := by
  linear_combination (norm := noncomm_ring)
    -x * hCx + d * hCx + hdx * C + 2 * x * hCd - 2 * d * hCd - 2 * hd * C

/-- The odd-cutoff square is an even square-variable annihilator. -/
theorem oddCutoff_square (x d C : A)
    (hdx : d * x = -(x * d)) (hd : d * d = 0)
    (hCx : C * x = x * C) (hCd : C * d = d * C) :
    ((x - d) * C) * ((x - d) * C) = x * x * (C * C) := by
  linear_combination (norm := noncomm_ring)
    x * hCx * C - d * hCx * C - x * hCd * C + d * hCd * C - hdx * C * C + hd * C * C

end OddMath.QuiverHecke.CyclotomicAction
