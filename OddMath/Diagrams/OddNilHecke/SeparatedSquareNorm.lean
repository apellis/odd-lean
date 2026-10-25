import OddMath.Diagrams.OddNilHecke.Intertwiner
import Mathlib.RingTheory.Nilpotent.Basic

/-! The polynomial norm on a zero/nonzero spectral corner is a unit.
This concerns the norm in the source corner, not an intertwiner endomorphism
of that corner: the intertwiner exchanges the two spectral corners. -/
namespace OddMath.OddNilHecke.Intertwiner
variable {A : Type*} [Ring A]

theorem squared_dots_commute {x y : A} (h : x * y + y * x = 0) :
    Commute (x ^ 2) (y ^ 2) := by
  have hyx : y * x = -(x * y) := eq_neg_of_add_eq_zero_right h
  have hyxa (a : A) : y * (x * a) = -(x * (y * a)) := by
    rw [← mul_assoc, hyx, neg_mul, mul_assoc]
  show x ^ 2 * y ^ 2 = y ^ 2 * x ^ 2
  noncomm_ring [hyx, hyxa]

theorem separated_square_norm_isUnit {x y : A}
    (hx : IsNilpotent (x ^ 2)) (hy : IsUnit (y ^ 2))
    (h : x * y + y * x = 0) :
    IsUnit (squareDiff x y) ∧ IsUnit (x ^ 2 + y ^ 2) ∧
      IsUnit (-(squareDiff x y ^ 2 * (x ^ 2 + y ^ 2))) := by
  have hc := squared_dots_commute h
  have hd : IsUnit (squareDiff x y) := by
    simpa only [squareDiff, sub_eq_add_neg] using
      hx.neg.isUnit_add_left_of_commute hy hc.neg_left
  have hs : IsUnit (x ^ 2 + y ^ 2) := hx.isUnit_add_right_of_commute hy hc
  exact ⟨hd, hs, ((hd.pow 2).mul hs).neg⟩

end OddMath.OddNilHecke.Intertwiner
