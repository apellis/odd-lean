import OddMath.Diagrams.OddNilHecke.DotTranslation
import OddMath.QuiverHecke.CyclotomicAction.Normality

/-!
# Simultaneous exterior translation: multicolour relation identities

Two independently chosen exterior coefficients may translate two odd colours
at once. The mixed dot relation, square-variable quadratic polynomials and
all alternating repeated-outer-colour braid monomials are preserved.
These identities are inputs to, not a construction of, the affine-category
translation equivalence or its cyclotomic quotient descent.
-/
namespace OddMath.QuiverHecke.CyclotomicAction.ExteriorTranslation

open OddMath.OddNilHecke.DotTranslation
variable {A : Type*} [Ring A]

/-- Independent translations preserve the mixed odd-dot relation. -/
theorem mixed_dots (x y d e : A)
    (hxy : x * y + y * x = 0) (hxe : x * e + e * x = 0)
    (hdy : d * y + y * d = 0) (hde : d * e + e * d = 0) :
    (x + d) * (y + e) + (y + e) * (x + d) = 0 := by
  linear_combination (norm := noncomm_ring) hxy + hxe + hdy + hde

/-- Anticommutation with an odd dot implies commutation with every even power. -/
theorem commute_even_power (d y : A) (hy : d * y + y * d = 0) (n : ℕ) :
    d * y ^ (2 * n) = y ^ (2 * n) * d := by
  have hs : Commute d (y ^ 2) := by
    change d * y ^ 2 = y ^ 2 * d
    linear_combination (norm := noncomm_ring) hy * y - y * hy
  simpa only [pow_mul] using (hs.pow_right n).eq

/-- Every square-variable mixed polynomial is fixed, with both translations active. -/
theorem quadratic_polynomial {J : Type*} (s : Finset J)
    (c : J → A) (m n : J → ℕ) (x y d e : A)
    (hd : d * d = 0) (hxd : x * d + d * x = 0)
    (he : e * e = 0) (hye : y * e + e * y = 0) :
    (∑ j ∈ s, c j * (x + d) ^ (2 * m j) * (y + e) ^ (2 * n j)) =
      ∑ j ∈ s, c j * x ^ (2 * m j) * y ^ (2 * n j) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [even_pow x d hd hxd, even_pow y e he hye]

/-- Repeated outer odd colour and a simultaneously translated middle odd colour.
The entire alternating correction is preserved for arbitrary even exponents. -/
theorem repeated_outer_braid (x y z d e : A) (m n : ℕ)
    (hd : d * d = 0) (hxd : x * d + d * x = 0)
    (hzd : z * d + d * z = 0) (hdy : d * y + y * d = 0)
    (he : e * e = 0) (hye : y * e + e * y = 0) :
    braidPolynomial (x + d) ((y + e) ^ (2 * n)) (z + d) m =
      braidPolynomial x (y ^ (2 * n)) z m := by
  rw [even_pow y e he hye]
  exact braidPolynomial_translate x (y ^ (2 * n)) z d m hd hxd hzd
    (commute_even_power d y hdy n)

/-- The coefficient parity involution in the odd-cutoff normalizer is essential. -/
theorem odd_normalizer_involutive_dot (x d : A) :
    (x - 2 * d) - 2 * (-d) = x := by noncomm_ring

/-- An odd coefficient supercommutes with the odd-cutoff polynomial. -/
theorem odd_coefficient_normality (a x d C : A)
    (hax : a * x + x * a = 0) (had : a * d + d * a = 0)
    (haC : a * C = C * a) :
    a * ((x - d) * C) = -(((x - d) * C) * a) := by
  linear_combination (norm := noncomm_ring) hax * C - had * C - x * haC + d * haC

/-- Exterior coefficients represented on `1,d,e,de`. -/
abbrev ExteriorMatrices := Matrix (Fin 4) (Fin 4) ℚ

def firstExterior : ExteriorMatrices :=
  !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0]

def secondExterior : ExteriorMatrices :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 1, 0, 0, 0; 0, -1, 0, 0]

theorem firstExterior_square : firstExterior * firstExterior = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstExterior, Matrix.mul_apply, Fin.sum_univ_succ]

theorem secondExterior_square : secondExterior * secondExterior = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondExterior, Matrix.mul_apply, Fin.sum_univ_succ]

theorem exterior_anticommute :
    firstExterior * secondExterior + secondExterior * firstExterior = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstExterior, secondExterior, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The two-parameter test does not kill the product of exterior coefficients. -/
theorem exterior_product_ne_zero : firstExterior * secondExterior ≠ 0 := by
  intro h
  have he := congrArg (fun m : ExteriorMatrices => m 3 0) h
  norm_num [firstExterior, secondExterior, Matrix.mul_apply, Fin.sum_univ_succ] at he

/-- A concrete simultaneous two-colour mixed-dot consumer. -/
theorem translated_exterior_dots :
    (firstExterior + firstExterior) * (secondExterior + secondExterior) +
      (secondExterior + secondExterior) * (firstExterior + firstExterior) = 0 :=
  mixed_dots _ _ _ _ exterior_anticommute exterior_anticommute
    exterior_anticommute exterior_anticommute

/-- A nonzero repeated-outer-colour correction survives the translation. -/
theorem translated_exterior_braid :
    braidPolynomial (firstExterior + firstExterior)
      ((secondExterior + secondExterior) ^ (2 * 0)) (0 + firstExterior) 1 =
      firstExterior := by
  rw [repeated_outer_braid firstExterior secondExterior 0 firstExterior secondExterior 1 0
    firstExterior_square (by rw [firstExterior_square]; simp) (by simp)
    exterior_anticommute secondExterior_square (by rw [secondExterior_square]; simp)]
  simp [braidPolynomial, Finset.sum_range_succ]

end OddMath.QuiverHecke.CyclotomicAction.ExteriorTranslation
