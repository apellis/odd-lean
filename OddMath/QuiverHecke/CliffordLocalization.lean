/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CliffordCoefficients
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Localized scalars for polynomial–Clifford coefficients

Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2, §3.4, localizes polynomial
coefficients at all differences and sums of distinct variables. We use the
larger total quotient ring, into which the polynomial ring embeds over any
commutative ground ring. Both required kinds of denominator are regular:
a transvection carries an individual variable to its sum with a scalar
multiple of another variable.

Reflections of individual variables extend to this localization. No square
root of minus one, field hypothesis, or invertibility of two is used.
This module does not construct the twisted symmetric-group extension or an
`Hn` action.
-/

noncomputable section
open scoped nonZeroDivisors TensorProduct
namespace OddMath.QuiverHecke.CliffordLocalization

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The ordinary polynomial scalar ring, before Clifford generators are added. -/
abbrev P := MvPolynomial (Fin n) R

/-- The total quotient ring: a faithful enlargement of KKT's scalar localization. -/
abbrev K := FractionRing (P R n)

/-- Polynomial scalars remain distinguishable after localization. -/
theorem algebraMap_injective : Function.Injective (algebraMap (P R n) (K R n)) :=
  IsFractionRing.injective (P R n) (K R n)

variable {R n}

/-- Reflection of one ordinary polynomial variable. -/
def reflection (i : Fin n) : P R n ≃ₐ[R] P R n :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun j => if j = i then -MvPolynomial.X j else MvPolynomial.X j)
    (MvPolynomial.aeval fun j => if j = i then -MvPolynomial.X j else MvPolynomial.X j)
    (by ext j; by_cases h : j = i <;> simp [h])
    (by ext j; by_cases h : j = i <;> simp [h])

@[simp] theorem reflection_X (i j : Fin n) :
    reflection (R := R) i (MvPolynomial.X j) =
      if j = i then -MvPolynomial.X j else MvPolynomial.X j := by
  simp [reflection]

/-- A polynomial change of variables carrying `Xᵢ` to `Xᵢ + a Xⱼ`. -/
def transvection (i j : Fin n) (hij : i ≠ j) (a : R) : P R n ≃ₐ[R] P R n :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun k => if k = i then
      MvPolynomial.X i + MvPolynomial.C a * MvPolynomial.X j else MvPolynomial.X k)
    (MvPolynomial.aeval fun k => if k = i then
      MvPolynomial.X i - MvPolynomial.C a * MvPolynomial.X j else MvPolynomial.X k)
    (by ext k; by_cases h : k = i <;> simp [h, Ne.symm hij])
    (by ext k; by_cases h : k = i <;> simp [h, Ne.symm hij])

@[simp] theorem transvection_X_self (i j : Fin n) (hij : i ≠ j) (a : R) :
    transvection i j hij a (MvPolynomial.X i) =
      MvPolynomial.X i + MvPolynomial.C a * MvPolynomial.X j := by
  simp [transvection]

/-- All scalar transvections of distinct variables are regular polynomials. -/
theorem X_add_C_mul_X_regular (i j : Fin n) (hij : i ≠ j) (a : R) :
    MvPolynomial.X i + MvPolynomial.C a * MvPolynomial.X j ∈ (P R n)⁰ := by
  have h := MulEquivClass.map_nonZeroDivisors (transvection i j hij a)
  rw [← h]
  exact ⟨MvPolynomial.X i, MvPolynomial.isRegular_X.mem_nonZeroDivisors,
    transvection_X_self i j hij a⟩

/-- The localized ordinary variable. -/
def y (i : Fin n) : K R n := algebraMap (P R n) (K R n) (MvPolynomial.X i)

/-- All KKT difference denominators become units. -/
theorem isUnit_y_sub (i j : Fin n) (hij : i ≠ j) :
    IsUnit (y (R := R) i - y j) := by
  have h := X_add_C_mul_X_regular i j hij (-1 : R)
  simp only [map_neg, map_one, neg_one_mul, ← sub_eq_add_neg] at h
  simpa only [y, map_sub] using IsLocalization.map_units (K R n)
    (⟨MvPolynomial.X i - MvPolynomial.X j, h⟩ : (P R n)⁰)

/-- All KKT sum denominators become units, also in characteristic two. -/
theorem isUnit_y_add (i j : Fin n) (hij : i ≠ j) :
    IsUnit (y (R := R) i + y j) := by
  have h := X_add_C_mul_X_regular i j hij (1 : R)
  simp only [map_one, one_mul] at h
  simpa only [y, map_add] using IsLocalization.map_units (K R n)
    (⟨MvPolynomial.X i + MvPolynomial.X j, h⟩ : (P R n)⁰)

/-- Reflection extends to the total quotient ring. -/
def reflect (i : Fin n) : K R n ≃ₐ[R] K R n :=
  IsFractionRing.algEquivOfAlgEquiv (reflection i)

@[simp] theorem reflect_y (i j : Fin n) :
    reflect (R := R) i (y j) = if j = i then -y j else y j := by
  by_cases h : j = i <;> simp [reflect, y, h]

/-- Extended reflection is involutive. -/
theorem reflect_involutive (i : Fin n) : Function.Involutive (reflect (R := R) i) := by
  have h : (reflect (R := R) i).toAlgHom.comp (reflect i).toAlgHom = AlgHom.id R (K R n) := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (P R n))
    ext j
    change reflect i (reflect i (y j)) = y (R := R) j
    by_cases h : j = i <;> simp [h]
  intro x
  exact DFunLike.congr_fun h x

/-- Different coordinate reflections commute. -/
theorem reflect_commute (i j : Fin n) :
    Function.Commute (reflect (R := R) i) (reflect j) := by
  have h : (reflect (R := R) i).toAlgHom.comp (reflect j).toAlgHom =
      (reflect j).toAlgHom.comp (reflect i).toAlgHom := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (P R n))
    ext k
    change reflect i (reflect j (y k)) = reflect (R := R) j (reflect i (y k))
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all
  intro x
  exact DFunLike.congr_fun h x

/-- The localized polynomial–Clifford coefficient module. -/
abbrev Coeff := K R n ⊗[R] CliffordCoefficients.Cl R n

/-- Multiplication by a localized scalar on the polynomial tensor factor. -/
def scalar (f : K R n) : Module.End R (Coeff (R := R) (n := n)) :=
  TensorProduct.map (Algebra.lmul R (K R n) f) LinearMap.id

@[simp] theorem scalar_tmul (f g : K R n) (v : CliffordCoefficients.Cl R n) :
    scalar f (g ⊗ₜ[R] v) = (f * g) ⊗ₜ[R] v := by simp [scalar]

/-- Composition of localized scalar operators is scalar multiplication. -/
theorem scalar_mul (f g : K R n) : scalar (f * g) = scalar f * scalar g := by
  apply TensorProduct.ext'
  intro h v
  simp [Module.End.mul_apply, mul_assoc]

@[simp] theorem scalar_one : scalar (1 : K R n) = 1 := by
  apply TensorProduct.ext'
  intro h v
  simp

/-- Localized Clifford multiplication, including the coordinate reflection. -/
def C (i : Fin n) : Module.End R (Coeff (R := R) (n := n)) :=
  TensorProduct.map (reflect i).toLinearMap
    (Algebra.lmul R (CliffordCoefficients.Cl R n) (CliffordCoefficients.c R n i))

@[simp] theorem C_tmul (i : Fin n) (f : K R n) (v : CliffordCoefficients.Cl R n) :
    C i (f ⊗ₜ[R] v) = reflect i f ⊗ₜ[R] (CliffordCoefficients.c R n i * v) := by
  simp [C]

/-- The full scalar–Clifford relation, including rational scalar expressions. -/
theorem C_scalar (i : Fin n) (f : K R n) :
    C i * scalar f = scalar (reflect i f) * C i := by
  apply TensorProduct.ext'
  intro g v
  simp [Module.End.mul_apply]

/-- Localized Clifford operators still square to one. -/
@[simp] theorem C_sq (i : Fin n) : C (R := R) i * C i = 1 := by
  apply TensorProduct.ext'
  intro f v
  simp [Module.End.mul_apply, reflect_involutive i f, ← mul_assoc]

/-- Distinct localized Clifford operators anticommute. -/
theorem C_anticommute (i j : Fin n) (hij : i ≠ j) :
    C (R := R) i * C j = -(C j * C i) := by
  apply TensorProduct.ext'
  intro f v
  simp only [Module.End.mul_apply, LinearMap.neg_apply, C_tmul]
  rw [reflect_commute i j f, ← mul_assoc,
    CliffordCoefficients.c_anticommute R n i j hij, neg_mul, TensorProduct.tmul_neg]
  simp only [mul_assoc]

/-- Multiplication by an inverse localized scalar is a two-sided inverse operator. -/
theorem scalar_inverse (f : K R n) (hf : IsUnit f) :
    scalar f * scalar (Ring.inverse f) = 1 ∧ scalar (Ring.inverse f) * scalar f = 1 := by
  constructor
  · rw [← scalar_mul, Ring.mul_inverse_cancel f hf, scalar_one]
  · rw [← scalar_mul, Ring.inverse_mul_cancel f hf, scalar_one]

/-- Both denominator operators needed in KKT (3.12) are invertible. -/
theorem denominator_inverses (i j : Fin n) (hij : i ≠ j) :
    (scalar (y (R := R) i - y j) * scalar (Ring.inverse (y i - y j)) = 1) ∧
    (scalar (y (R := R) i + y j) * scalar (Ring.inverse (y i + y j)) = 1) :=
  ⟨(scalar_inverse _ (isUnit_y_sub i j hij)).1,
    (scalar_inverse _ (isUnit_y_add i j hij)).1⟩

end OddMath.QuiverHecke.CliffordLocalization
