import OddMath.QuiverHecke.SwappedAssembly.Sigma.FiniteBendEvaluation

/-! # Arithmetic for the mixed-bend series comparison

The chart changes and the PR minus in `SwappedHomInversion.md` §3 (4)–(6)
use these identities in arbitrary endomorphism rings. No commutativity
of the probe and reservoir dots is assumed here.
-/
noncomputable section
open scoped BigOperators
namespace OddMath.QuiverHecke.SwappedAssembly

section Ring
variable {A A' : Type*} [Ring A] [Ring A']

/-- A specified right inverse of a unit is its ring inverse. -/
theorem bend_inverse_eq {x z : A} (hx : IsUnit x) (hz : x * z = 1) :
    Ring.inverse x = z := by
  calc
    Ring.inverse x = Ring.inverse x * (x * z) := by rw [hz, mul_one]
    _ = z := by rw [← mul_assoc, Ring.inverse_mul_cancel x hx, one_mul]

/-- Negating a unit negates its inverse, also in a zero ring. -/
theorem bend_inverse_neg {x : A} (hx : IsUnit x) :
    Ring.inverse (-x) = -Ring.inverse x := by
  apply bend_inverse_eq hx.neg
  rw [neg_mul_neg, Ring.mul_inverse_cancel x hx]

/-- Negating both chart dots contributes exactly one minus to a
consecutive inverse-probe/reservoir monomial. -/
theorem bend_neg_monomial (a b : A) (r : ℕ) :
    (-a) ^ (r+1) * (-b) ^ r = -(a ^ (r+1) * b ^ r) := by
  rw [neg_pow' a, neg_pow b, mul_assoc, ← mul_assoc ((-1 : A) ^ (r+1)), ← pow_add]
  have he : r + 1 + r = 2*r+1 := by omega
  rw [he, pow_add (-1 : A) (2*r) 1, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
  simp only [neg_mul, one_mul, mul_neg]

/-- The odd coefficient chart therefore contributes its one prescribed
minus before applying the additive bend insertion. -/
theorem bend_inverse_neg_monomial {x : A} (hx : IsUnit x) (y : A) (r : ℕ) :
    Ring.inverse (-x) ^ (r+1) * (-y) ^ r =
      -(Ring.inverse x ^ (r+1) * y ^ r) := by
  rw [bend_inverse_neg hx, bend_neg_monomial]

end Ring

section Additive
variable {A G : Type*} [Ring A] [AddCommGroup G]

/-- The ring's alternating coefficient becomes the integer scalar of
the residual comparison under every additive insertion. -/
theorem bendInsertion_alternating (β : A →+ G) (r : ℕ) (z : A) :
    β ((-1 : A)^r * z) = ((-1 : ℤ)^r) • β z := by
  have h : (-1 : A)^r * z = ((-1 : ℤ)^r) • z := by
    simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [h, map_zsmul]

/-- The alternating XP-to-YR series has the literal negative
`q^(r+1)` convention at odd parity. -/
theorem bend_odd_probe_series (β : A →+ G) (z : ℕ → A) (n : ℕ) :
    (∑ r ∈ Finset.range n, β ((-1 : A)^r * z r)) =
      -∑ r ∈ Finset.range n, ((-1 : ℤ)^(r+1)) • β (z r) := by
  simp only [bendInsertion_alternating, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
    neg_neg]

end Additive
end OddMath.QuiverHecke.SwappedAssembly
