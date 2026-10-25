import OddMath.Diagrams.OddNilHecke.SeparatedSquareNorm
import Mathlib.Algebra.Group.Commute.Units

/-!
# The diagonal crossing on a separated odd-dot corner

For anticommuting dots and an invertible squared difference, the rational
operator `(x-y)/(x²-y²)` satisfies both inhomogeneous dot slides. Its square
is the coefficient cancelled by the two off-diagonal shuffle entries.
This is a local algebra identity for the separated-sector construction in
`docs/Nondegeneracy/SeparatedFusion.md`, not a categorical fusion theorem.
-/

namespace OddMath.OddNilHecke.Intertwiner

variable {A : Type*} [Ring A]

/-- Each odd dot commutes with the inverse squared difference. -/
theorem commute_inverse_square_difference {x y : A} (h : x * y + y * x = 0)
    (u : Aˣ) (hu : (u : A) = x ^ 2 - y ^ 2) :
    Commute x (↑u⁻¹ : A) ∧ Commute y (↑u⁻¹ : A) := by
  have hyx : y * x = -(x * y) := eq_neg_of_add_eq_zero_right h
  have hyxa (a : A) : y * (x * a) = -(x * (y * a)) := by
    rw [← mul_assoc, hyx, neg_mul, mul_assoc]
  have hx : Commute x (u : A) := by
    rw [hu]
    show x * (x ^ 2 - y ^ 2) = (x ^ 2 - y ^ 2) * x
    noncomm_ring [hyx, hyxa]
  have hy : Commute y (u : A) := by
    rw [hu]
    show y * (x ^ 2 - y ^ 2) = (x ^ 2 - y ^ 2) * y
    noncomm_ring [hyx, hyxa]
  exact ⟨hx.units_inv_right, hy.units_inv_right⟩

/-- Both odd slides and the square of the position-preserving crossing.
The off-diagonal shuffle entries must cancel this square, not be identities
in both directions. -/
theorem separated_diagonal_crossing {x y : A} (h : x * y + y * x = 0)
    (u : Aˣ) (hu : (u : A) = x ^ 2 - y ^ 2) :
    let a := (x - y) * (↑u⁻¹ : A)
    a * x + y * a = 1 ∧ a * y + x * a = 1 ∧
      a ^ 2 = (x ^ 2 + y ^ 2) * (↑u⁻¹ : A) ^ 2 := by
  obtain ⟨hx, hy⟩ := commute_inverse_square_difference h u hu
  have hi : (x ^ 2 - y ^ 2) * (↑u⁻¹ : A) = 1 := by
    rw [← hu]
    exact u.val_inv
  have hyx : y * x = -(x * y) := eq_neg_of_add_eq_zero_right h
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · calc
      (x - y) * (↑u⁻¹ : A) * x + y * ((x - y) * (↑u⁻¹ : A)) =
          (x ^ 2 - y ^ 2) * (↑u⁻¹ : A) := by noncomm_ring [hx.symm.eq]
      _ = 1 := hi
  · calc
      (x - y) * (↑u⁻¹ : A) * y + x * ((x - y) * (↑u⁻¹ : A)) =
          (x ^ 2 - y ^ 2) * (↑u⁻¹ : A) := by noncomm_ring [hy.symm.eq]
      _ = 1 := hi
  · rw [(hx.sub_left hy).mul_pow]
    congr 1
    noncomm_ring [hyx]

end OddMath.OddNilHecke.Intertwiner
