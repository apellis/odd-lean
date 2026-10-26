/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRightCoefficient
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Finite right polynomial operators for the moving-strand map

For KKO I, arXiv:1206.5933v2, Proposition 8.4, evaluate ordered finite
polynomials `∑ t^m ⊗ c_m` on the existing source and target quotients.
The order is dot first, coefficient second; composition reverses products.
For homogeneous `b` of degree `q`, multiplying the monomials `t^r ⊗ b`
and `t^s ⊗ c` contributes `(-1)^(s p(i) q)`. All natural exponents
are retained, with no square-zero relation on an odd variable.

This module proves finite-sum equivariance and the signed monomial action
law. The coefficient family is a finitely supported function, not yet a
bundled supertensor algebra. Its multiplication and comparison with the
source's `k[t_i]` supertensor cyclotomic algebra remain to be supplied.
Mathlib's `SkewPolynomial` uses the alternative order `c t^m`.
The finite-colour, positive-height and polynomial-parity restrictions remain.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

private theorem dot_pow_coefficient {V : Type*} [AddCommGroup V] [Module k V]
    (T C : Module.End k V) (e : k) (h : T * C = e • (C * T)) (s : ℕ) :
    T ^ s * C = e ^ s • (C * T ^ s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc, h,
      smul_mul_assoc, smul_smul, ← pow_succ', mul_assoc, ← pow_succ]
    rw [← pow_succ']

private theorem monomial_comp {V : Type*} [AddCommGroup V] [Module k V]
    (T B C BC : Module.End k V) (e : k)
    (h : T * B = e • (B * T)) (hm : C * B = BC) (r s : ℕ) :
    (C * T ^ s) * (B * T ^ r) = e ^ s • (BC * T ^ (r + s)) := by
  rw [mul_assoc C, ← mul_assoc (T ^ s), dot_pow_coefficient T B e h,
    smul_mul_assoc, mul_smul_comm, mul_assoc B, ← pow_add, Nat.add_comm s r,
    ← mul_assoc, hm]

/-- Finite coefficients in the order `t^m ⊗ c_m`; no multiplication is declared. -/
abbrev RightPolynomialCoefficients (a : I → _root_.Polynomial k) (n : ℕ) :=
  ℕ →₀ CyclotomicAlgebra D Sc a n

/-- The ordered monomial `t^m ⊗ c` acts by dots followed by the coefficient. -/
def sourceRightMonomial (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (m : ℕ) :
    CyclotomicAlgebra D Sc a n →+ Module.End k (qSourceSpace D Sc i a ha n) where
  toFun c := sourceRightCoefficientLinear D Sc i a ha n c * sourceRightDotLinear D Sc i a ha n ^ m
  map_zero' := by
    have h : sourceRightCoefficientLinear D Sc i a ha n 0 = 0 := by
      ext z
      exact LinearMap.congr_fun (sourceRightCoefficient_zero D Sc i a n) z
    rw [h, zero_mul]
  map_add' b c := by
    have h : sourceRightCoefficientLinear D Sc i a ha n (b + c) =
        sourceRightCoefficientLinear D Sc i a ha n b + sourceRightCoefficientLinear D Sc i a ha n c := by
      ext z
      exact LinearMap.congr_fun (sourceRightCoefficient_add D Sc i a n b c) z
    rw [h, add_mul]

/-- Evaluation of every finite ordered polynomial on the same quotient carrier. -/
def sourceRightPolynomial (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    RightPolynomialCoefficients D Sc a n →+ Module.End k (qSourceSpace D Sc i a ha n) :=
  Finsupp.liftAddHom (sourceRightMonomial D Sc i a ha n)

@[simp] theorem sourceRightPolynomial_single (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (m : ℕ)
    (c : CyclotomicAlgebra D Sc a n) :
    sourceRightPolynomial D Sc i a ha n (Finsupp.single m c) = sourceRightMonomial D Sc i a ha n m c := by
  simp [sourceRightPolynomial]

/-- The constant unit acts as the identity. -/
theorem sourceRightPolynomial_one (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    sourceRightPolynomial D Sc i a ha n (Finsupp.single 0 1) = 1 := by
  rw [sourceRightPolynomial_single]
  change sourceRightCoefficientLinear D Sc i a ha n 1 * _ ^ 0 = 1
  simp only [pow_zero, mul_one]
  ext z
  exact LinearMap.congr_fun (sourceRightCoefficient_one D Sc i a n) z

/-- Signed multiplication of ordered monomial operators; the coefficient of
    the first monomial passes the dot power of the second. -/
theorem sourceRightMonomial_comp (i : I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (r s : ℕ) (q : ZMod 2) (b c : CyclotomicAlgebra D Sc a n)
    (hb : b ∈ cyclotomicParity D Sc a ha n q) :
    sourceRightMonomial D Sc i a ha n s c * sourceRightMonomial D Sc i a ha n r b =
      sign k (D.parity i * q) ^ s • sourceRightMonomial D Sc i a ha n (r + s) (b * c) := by
  apply monomial_comp
  · exact sourceRightDot_coefficient D Sc i a ha n q b hb
  · ext z
    exact (LinearMap.congr_fun (sourceRightCoefficient_mul D Sc i a n b c) z).symm

/-- The ordered monomial `t^m ⊗ c` acts by dots followed by the coefficient. -/
def targetRightMonomial (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (m : ℕ) :
    CyclotomicAlgebra D Sc a n →+ Module.End k (qTargetSpace D Sc i β a ha n) where
  toFun c := targetRightCoefficientLinear D Sc i β a ha n c * targetRightDotLinear D Sc i β a ha n ^ m
  map_zero' := by
    have h : targetRightCoefficientLinear D Sc i β a ha n 0 = 0 := by
      ext z
      exact LinearMap.congr_fun (targetRightCoefficient_zero D Sc i β a ha n) z
    rw [h, zero_mul]
  map_add' b c := by
    have h : targetRightCoefficientLinear D Sc i β a ha n (b + c) =
        targetRightCoefficientLinear D Sc i β a ha n b + targetRightCoefficientLinear D Sc i β a ha n c := by
      ext z
      exact LinearMap.congr_fun (targetRightCoefficient_add D Sc i β a ha n b c) z
    rw [h, add_mul]

/-- Evaluation of every finite ordered polynomial on the same quotient carrier. -/
def targetRightPolynomial (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    RightPolynomialCoefficients D Sc a n →+ Module.End k (qTargetSpace D Sc i β a ha n) :=
  Finsupp.liftAddHom (targetRightMonomial D Sc i β a ha n)

@[simp] theorem targetRightPolynomial_single (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (m : ℕ)
    (c : CyclotomicAlgebra D Sc a n) :
    targetRightPolynomial D Sc i β a ha n (Finsupp.single m c) = targetRightMonomial D Sc i β a ha n m c := by
  simp [targetRightPolynomial]

/-- The constant unit acts as the identity. -/
theorem targetRightPolynomial_one (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) :
    targetRightPolynomial D Sc i β a ha n (Finsupp.single 0 1) = 1 := by
  rw [targetRightPolynomial_single]
  change targetRightCoefficientLinear D Sc i β a ha n 1 * _ ^ 0 = 1
  simp only [pow_zero, mul_one]
  ext z
  exact LinearMap.congr_fun (targetRightCoefficient_one D Sc i β a ha n) z

/-- Signed multiplication of ordered monomial operators; the coefficient of
    the first monomial passes the dot power of the second. -/
theorem targetRightMonomial_comp (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ)
    (r s : ℕ) (q : ZMod 2) (b c : CyclotomicAlgebra D Sc a n)
    (hb : b ∈ cyclotomicParity D Sc a ha n q) :
    targetRightMonomial D Sc i β a ha n s c * targetRightMonomial D Sc i β a ha n r b =
      sign k (D.parity i * q) ^ s • targetRightMonomial D Sc i β a ha n (r + s) (b * c) := by
  apply monomial_comp
  · exact targetRightDot_coefficient D Sc i β a ha n q b hb
  · ext z
    exact (LinearMap.congr_fun (targetRightCoefficient_mul D Sc i β a ha n b c) z).symm

/-- Q intertwines ordered monomials of every natural degree. -/
theorem rightMonomial_Q (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n m : ℕ) (c : CyclotomicAlgebra D Sc a n) :
    (targetRightMonomial D Sc i β a ha n m c).comp (parityCyclotomicContentQLinear D Sc i β a ha n) =
      (parityCyclotomicContentQLinear D Sc i β a ha n).comp (sourceRightMonomial D Sc i a ha n m c) := by
  have hd := rightDot_Q_square D Sc i β a ha n
  have hp : ∀ m, (targetRightDotLinear D Sc i β a ha n ^ m).comp
      (parityCyclotomicContentQLinear D Sc i β a ha n) =
      (parityCyclotomicContentQLinear D Sc i β a ha n).comp
        (sourceRightDotLinear D Sc i a ha n ^ m) := by
    intro m
    induction m with
    | zero => ext z; rfl
    | succ m ih =>
      simp only [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc]
      rw [ih, ← LinearMap.comp_assoc, hd, LinearMap.comp_assoc]
  have hc : (targetRightCoefficientLinear D Sc i β a ha n c).comp
      (parityCyclotomicContentQLinear D Sc i β a ha n) =
      (parityCyclotomicContentQLinear D Sc i β a ha n).comp
        (sourceRightCoefficientLinear D Sc i a ha n c) := by
    ext z
    exact LinearMap.congr_fun (rightCoefficient_Q D Sc i β a ha n c) z
  simp only [targetRightMonomial, sourceRightMonomial, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Module.End.mul_eq_comp, LinearMap.comp_assoc]
  rw [hp, ← LinearMap.comp_assoc, hc, LinearMap.comp_assoc]

/-- Q is equivariant for every finite polynomial, without assuming any new action laws. -/
theorem rightPolynomial_Q (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
    (ha : CyclotomicPolynomialParity D a) (n : ℕ) (f : RightPolynomialCoefficients D Sc a n) :
    (targetRightPolynomial D Sc i β a ha n f).comp (parityCyclotomicContentQLinear D Sc i β a ha n) =
      (parityCyclotomicContentQLinear D Sc i β a ha n).comp (sourceRightPolynomial D Sc i a ha n f) := by
  induction f using Finsupp.induction with
  | zero => simp
  | @single_add m c f _ _ ih =>
    simp only [map_add, sourceRightPolynomial_single, targetRightPolynomial_single,
      LinearMap.add_comp, LinearMap.comp_add, rightMonomial_Q, ih]

end OddMath.QuiverHecke
