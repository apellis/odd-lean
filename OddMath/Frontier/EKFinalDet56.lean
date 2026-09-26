import OddMath.Frontier.EKFinalRibbonDet
import OddMath.Frontier.EKFinalPrinted

/-!
# EK §5.2: the Gram determinants in degrees 5 and 6

Source: Ellis–Khovanov, arXiv:1107.5610v2, §5.2, pp. 39–40.

The Gram determinant of the form (2.1) on `Λ'_n` in the basis `h_α` (`EKGeneralQNondeg.gram`),
as an element of `ℤ[q]`:

* `det_gram_five`:
  `det G₅ = q⁴⁹ (q-1)¹⁴ (q+1)¹² f₆² (q²+q+1)² (q²-q+1) f₁₈`;
* `det_gram_six`:
  `det G₆ = q¹²⁹ (q-1)³⁸ (q+1)³⁴ f₆⁵ (q²+q+1)⁶ (q²-q+1)⁴ f₁₈² (q²+1)² φ₂₂ f₅₀`.

These are exactly the printed multiplicities of pp. 39–40 in degrees 5 and 6 (`printedFactors`),
with leading coefficient `+1`.

Method (`EKFinalRibbonDet.gram_det_eq_of_ribbonCheck`): both sides are integer polynomials
whose coefficients are bounded a priori; they agree at `q = 2^K` (Kronecker substitution),
where the left side is computed from (2.33) as a determinant of an integer matrix indexed by
the compositions, certified by a triangular factorization.
-/

open Polynomial

namespace OddMath.Frontier.EKFinal
open EKGeneralQ

set_option maxRecDepth 100000 in
theorem ribbonCheck_five : ribbonCheck 5 48 (printedFactors 5) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ribbonCheck_six : ribbonCheck 6 136 (printedFactors 6) = true := by decide +kernel

/-- **EK §5.2, degree 5.** -/
theorem det_gram_five : (gram (X : ℤ[X]) 5).det =
    X ^ 49 * (X - 1) ^ 14 * (X + 1) ^ 12 * f6 ^ 2 * (X ^ 2 + X + 1) ^ 2 * (X ^ 2 - X + 1) *
      f18 := by
  rw [gram_det_eq_of_ribbonCheck (by norm_num) 48 _ ribbonCheck_five]
  simp only [printedFactors, prodPow, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, ofList_X, ofList_X_sub_one, ofList_X_add_one, ofList_phi3,
    ofList_phi6, pow_one]
  rw [show ofList f6L = f6 from rfl, show ofList f18L = f18 from rfl]
  simp only [mul_assoc]

/-- **EK §5.2, degree 6.** -/
theorem det_gram_six : (gram (X : ℤ[X]) 6).det =
    X ^ 129 * (X - 1) ^ 38 * (X + 1) ^ 34 * f6 ^ 5 * (X ^ 2 + X + 1) ^ 6 * (X ^ 2 - X + 1) ^ 4 *
      f18 ^ 2 * (X ^ 2 + 1) ^ 2 * phi22 * f50 := by
  rw [gram_det_eq_of_ribbonCheck (by norm_num) 136 _ ribbonCheck_six]
  simp only [printedFactors, prodPow, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, ofList_X, ofList_X_sub_one, ofList_X_add_one, ofList_phi3,
    ofList_phi6, ofList_phi4, pow_one]
  rw [show ofList f6L = f6 from rfl, show ofList f18L = f18 from rfl,
    show ofList phi22L = phi22 from rfl, show ofList f50L = f50 from rfl]
  simp only [mul_assoc]

/-- Degree 5 as the printed data: `det G₅ = ∏ (printed factor)^(multiplicity)`. -/
theorem det_gram_five_printed : (gram (X : ℤ[X]) 5).det = prodPow (printedFactors 5) :=
  gram_det_eq_of_ribbonCheck (by norm_num) 48 _ ribbonCheck_five

/-- Degree 6 as the printed data. -/
theorem det_gram_six_printed : (gram (X : ℤ[X]) 6).det = prodPow (printedFactors 6) :=
  gram_det_eq_of_ribbonCheck (by norm_num) 136 _ ribbonCheck_six

end OddMath.Frontier.EKFinal
