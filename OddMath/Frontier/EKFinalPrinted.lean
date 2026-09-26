import OddMath.Frontier.EKFinalDetCert

/-!
# EK §5.2: the printed minimal polynomials

Source: Ellis–Khovanov, arXiv:1107.5610v2, §5.2, pp. 39–40: "the minimal polynomials for the
values of `q` at which the `q`-bilinear form is degenerate, through degree 7", with
multiplicities.  For the longer polynomials the paper prints the coefficients from the top
degree down to the middle and continues palindromically; `palin` performs that continuation
(coefficients are listed from degree `0` upwards, which for a palindromic polynomial is the
printed list itself).

The printed factors, in order of appearance:

* degree 2: `q`; degree 3: `q - 1`, `q + 1`; degree 4: `f6 = q⁶ + 2q⁴ - q³ + 2q² + 1`;
* degree 5: `q² + q + 1`, `q² - q + 1`, `f18`;
* degree 6: `q² + 1`, `phi22 = q¹⁰ - q⁹ + ⋯ + 1`, `f50`;
* degree 7: `q⁴ + q³ + q² + q + 1`, `q⁶ + ⋯ + 1`, `q⁴ + 1`, `q⁴ - q³ + q² - q + 1`, `q⁴ - q² + 1`,
  `phi17 = q¹⁶ + ⋯ + 1`, `phi28 = q¹² - q¹⁰ + q⁸ - q⁶ + q⁴ - q² + 1`, `f102`.

`printedFactors n` is the printed factorization of the degree-`n` Gram determinant: each
factor with its printed multiplicity in degree `n`.
-/

noncomputable section
open Polynomial

namespace OddMath.Frontier.EKFinal

/-- Palindromic continuation of a coefficient list printed down to the middle. -/
def palin (l : List ℤ) : List ℤ := l ++ l.dropLast.reverse

/-- `q⁶ + 2q⁴ - q³ + 2q² + 1` (degree 4 of the list). -/
def f6L : List ℤ := [1, 0, 2, -1, 2, 0, 1]

/-- `q¹⁸ + q¹⁷ + 3q¹⁶ + 4q¹⁵ + 6q¹⁴ + 7q¹³ + 8q¹² + 10q¹¹ + 11q¹⁰ + 10q⁹ + …` (degree 5). -/
def f18L : List ℤ := palin [1, 1, 3, 4, 6, 7, 8, 10, 11, 10]

/-- The degree-50 polynomial of the list (degree 6), printed down to `34q²⁵`. -/
def f50L : List ℤ := palin [1, 1, 2, 2, 5, 4, 8, 6, 11, 9, 16, 16, 21, 14, 23, 24, 30, 23, 30,
  28, 38, 30, 34, 30, 39, 34]

/-- The degree-102 polynomial of the list (degree 7), printed down to `2080q⁵¹`. -/
def f102L : List ℤ := palin [1, -1, 4, -2, 9, -2, 18, -1, 34, 2, 58, 13, 88, 36, 134, 64, 204,
  99, 298, 155, 405, 238, 537, 330, 705, 442, 887, 584, 1089, 731, 1323, 881, 1572, 1050, 1808,
  1233, 2045, 1401, 2284, 1565, 2494, 1716, 2692, 1829, 2874, 1926, 2995, 2018, 3067, 2070, 3118,
  2080]

/-- `q¹⁰ - q⁹ + q⁸ - ⋯ + 1` (degree 6). -/
def phi22L : List ℤ := [1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1]

/-- `q¹⁶ + q¹⁵ + ⋯ + 1` (degree 7). -/
def phi17L : List ℤ := List.replicate 17 1

/-- `q¹² - q¹⁰ + q⁸ - q⁶ + q⁴ - q² + 1` (degree 7). -/
def phi28L : List ℤ := [1, 0, -1, 0, 1, 0, -1, 0, 1, 0, -1, 0, 1]

def f6 : ℤ[X] := ofList f6L
def f18 : ℤ[X] := ofList f18L
def f50 : ℤ[X] := ofList f50L
def f102 : ℤ[X] := ofList f102L
def phi22 : ℤ[X] := ofList phi22L
def phi17 : ℤ[X] := ofList phi17L
def phi28 : ℤ[X] := ofList phi28L

theorem f6_eq : f6 = X ^ 6 + 2 * X ^ 4 - X ^ 3 + 2 * X ^ 2 + 1 := by
  simp [f6, f6L, ofList]; ring

theorem f18_eq : f18 = X ^ 18 + X ^ 17 + 3 * X ^ 16 + 4 * X ^ 15 + 6 * X ^ 14 + 7 * X ^ 13 +
    8 * X ^ 12 + 10 * X ^ 11 + 11 * X ^ 10 + 10 * X ^ 9 + 11 * X ^ 8 + 10 * X ^ 7 + 8 * X ^ 6 +
    7 * X ^ 5 + 6 * X ^ 4 + 4 * X ^ 3 + 3 * X ^ 2 + X + 1 := by
  simp [f18, f18L, palin, ofList]; ring

theorem phi22_eq : phi22 = X ^ 10 - X ^ 9 + X ^ 8 - X ^ 7 + X ^ 6 - X ^ 5 + X ^ 4 - X ^ 3 +
    X ^ 2 - X + 1 := by
  simp [phi22, phi22L, ofList]; ring

theorem phi17_eq : phi17 = ∑ i ∈ Finset.range 17, X ^ i := by
  simp [phi17, phi17L, ofList, Finset.sum_range_succ]; ring

theorem phi28_eq : phi28 = X ^ 12 - X ^ 10 + X ^ 8 - X ^ 6 + X ^ 4 - X ^ 2 + 1 := by
  simp [phi28, phi28L, ofList]; ring

theorem ofList_X : ofList [0, 1] = X := by simp [ofList]
theorem ofList_X_sub_one : ofList [-1, 1] = X - 1 := by simp [ofList]; ring
theorem ofList_X_add_one : ofList [1, 1] = X + 1 := by simp [ofList]; ring
theorem ofList_phi3 : ofList [1, 1, 1] = X ^ 2 + X + 1 := by simp [ofList]; ring
theorem ofList_phi6 : ofList [1, -1, 1] = X ^ 2 - X + 1 := by simp [ofList]; ring
theorem ofList_phi4 : ofList [1, 0, 1] = X ^ 2 + 1 := by simp [ofList]; ring
theorem ofList_phi5 : ofList [1, 1, 1, 1, 1] = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  simp [ofList]; ring
theorem ofList_phi7 : ofList [1, 1, 1, 1, 1, 1, 1] =
    X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  simp [ofList]; ring
theorem ofList_phi8 : ofList [1, 0, 0, 0, 1] = X ^ 4 + 1 := by simp [ofList]; ring
theorem ofList_phi10 : ofList [1, -1, 1, -1, 1] = X ^ 4 - X ^ 3 + X ^ 2 - X + 1 := by
  simp [ofList]; ring
theorem ofList_phi12 : ofList [1, 0, -1, 0, 1] = X ^ 4 - X ^ 2 + 1 := by simp [ofList]; ring

/-- EK p. 39, "All of the polynomials are palindromic": this fails for the printed factors `q`
and `q - 1` (a palindromic polynomial of degree `1` has equal coefficients).  All the other
printed factors are palindromic (for the long ones by the printed convention `palin`). -/
theorem q_and_q_sub_one_not_palindromic :
    (X : ℤ[X]).coeff 0 ≠ (X : ℤ[X]).coeff 1 ∧
      (X - 1 : ℤ[X]).coeff 0 ≠ (X - 1 : ℤ[X]).coeff 1 := by
  simp [coeff_X, coeff_one]

/-- The printed factor list with multiplicities in degree `n` (`2 ≤ n ≤ 7`), p. 39–40. -/
def printedFactors : ℕ → List (List ℤ × ℕ)
  | 2 => [([0, 1], 1)]
  | 3 => [([0, 1], 5), ([-1, 1], 1), ([1, 1], 1)]
  | 4 => [([0, 1], 17), ([-1, 1], 4), ([1, 1], 4), (f6L, 1)]
  | 5 => [([0, 1], 49), ([-1, 1], 14), ([1, 1], 12), (f6L, 2), ([1, 1, 1], 2), ([1, -1, 1], 1),
      (f18L, 1)]
  | 6 => [([0, 1], 129), ([-1, 1], 38), ([1, 1], 34), (f6L, 5), ([1, 1, 1], 6), ([1, -1, 1], 4),
      (f18L, 2), ([1, 0, 1], 2), (phi22L, 1), (f50L, 1)]
  | 7 => [([0, 1], 321), ([-1, 1], 102), ([1, 1], 88), (f6L, 12), ([1, 1, 1], 18),
      ([1, -1, 1], 11), (f18L, 5), ([1, 0, 1], 8), (phi22L, 2), (f50L, 2),
      ([1, 1, 1, 1, 1], 2), ([1, 1, 1, 1, 1, 1, 1], 1), ([1, 0, 0, 0, 1], 1),
      ([1, -1, 1, -1, 1], 1), ([1, 0, -1, 0, 1], 1), (phi17L, 1), (phi28L, 1), (f102L, 1)]
  | _ => []

/-- The degrees of the printed factorizations: `Σ mult · deg = D(n) = 2^{n-2}(n² - 3n + 4) - 1`
(EK (5.2)) for `n = 2, …, 7`. -/
theorem printed_degrees :
    ∀ n ∈ [2, 3, 4, 5, 6, 7], ((printedFactors n).map fun f => (f.1.length - 1) * f.2).sum =
      2 ^ (n - 2) * (n ^ 2 + 4 - 3 * n) - 1 := by
  decide +kernel

end OddMath.Frontier.EKFinal
