/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Polynomial
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Tactic

/-!
# Polynomial–Clifford coefficient operators

Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2, §3.3, the coefficient
relations (ii)–(iii) of Definition 3.5, and Theorem 3.13, proof (a).
The coefficient module is the ordinary polynomial module tensored with the
Clifford algebra. A Clifford generator reflects its own polynomial variable.
Thus it anticommutes with that variable, not with the other variables.

This constructs the coefficient operators before localization, without colour
idempotents or crossing operators. It does not assert an action of `Hn`.
No invertibility of two or square root of minus one is needed here.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.QuiverHecke.CliffordCoefficients

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The Clifford form with orthogonal generators of square one. -/
def form : QuadraticForm R (Fin n → R) :=
  QuadraticMap.weightedSumSquares R (fun _ : Fin n => (1 : R))

/-- The Clifford coefficient algebra. -/
abbrev Cl := CliffordAlgebra (form R n)

/-- Its generator at position `i`. -/
def c (i : Fin n) : Cl R n := CliffordAlgebra.ι (form R n) (Pi.single i 1)

@[simp] theorem c_sq (i : Fin n) : c R n i * c R n i = 1 := by
  simp [c, CliffordAlgebra.ι_sq_scalar, form, Pi.single_apply]

theorem c_anticommute (i j : Fin n) (hij : i ≠ j) :
    c R n i * c R n j = -(c R n j * c R n i) := by
  rw [eq_neg_iff_add_eq_zero]
  unfold c
  rw [CliffordAlgebra.ι_mul_ι_add_swap]
  have hform : form R n (Pi.single i 1 + Pi.single j 1) = 2 := by
    simp only [form, QuadraticMap.weightedSumSquares_apply]
    simp only [smul_eq_mul, one_mul, ← pow_two]
    have heq : (fun k : Fin n => (Pi.single i (1 : R) k + Pi.single j 1 k) ^ 2) =
        fun k => (Pi.single i (1 : R) : Fin n → R) k + (Pi.single j (1 : R) : Fin n → R) k := by
      funext k
      by_cases hi : k = i <;> by_cases hj : k = j <;>
        simp_all
    calc
      _ = ∑ k : Fin n, ((Pi.single i (1 : R) : Fin n → R) k +
          (Pi.single j (1 : R) : Fin n → R) k) :=
        Finset.sum_congr rfl (fun k _ => congrFun heq k)
      _ = 2 := by rw [Finset.sum_add_distrib]; simp; ring
  change algebraMap R _ (form R n (Pi.single i 1 + Pi.single j 1) -
    form R n (Pi.single i 1) - form R n (Pi.single j 1)) = 0
  rw [hform]
  simp [form, Pi.single_apply, show (2 : R) - 1 - 1 = 0 by ring]

/-- Ordinary polynomial coefficients with values in the Clifford algebra.
This is the polynomial–Clifford tensor product as an `R`-module. -/
abbrev Coeff := (Fin n → ℕ) →₀ Cl R n

variable {R n}

/-- A normal-ordered polynomial monomial with Clifford coefficient. -/
def monomial (a : Fin n → ℕ) (v : Cl R n) : Coeff R n := Finsupp.single a v

/-- Multiplication by the ordinary polynomial variable. -/
def Y (i : Fin n) : Module.End R (Coeff R n) :=
  Finsupp.lsum R fun a => Finsupp.lsingle (a + SkewPolynomial.expSingle i)

/-- Clifford multiplication together with reflection of the matching variable. -/
def C (i : Fin n) : Module.End R (Coeff R n) :=
  Finsupp.lsum R fun a => (Finsupp.lsingle a).comp
    (((-1 : R) ^ a i) • Algebra.lmul R (Cl R n) (c R n i))

@[simp] theorem Y_monomial (i : Fin n) (a : Fin n → ℕ) (v : Cl R n) :
    Y i (monomial a v) = monomial (a + SkewPolynomial.expSingle i) v := by
  simp [Y, monomial]

@[simp] theorem C_monomial (i : Fin n) (a : Fin n → ℕ) (v : Cl R n) :
    C i (monomial a v) = monomial a (((-1 : R) ^ a i) • (c R n i * v)) := by
  simp [C, monomial]

/-- Equality of coefficient operators can be checked on normal-ordered monomials. -/
theorem ext {f g : Module.End R (Coeff R n)}
    (h : ∀ a v, f (monomial a v) = g (monomial a v)) : f = g := by
  exact Finsupp.lhom_ext h

/-- Ordinary polynomial variables commute. -/
theorem Y_commute (i j : Fin n) : Commute (Y (R := R) i) (Y j) := by
  apply ext
  intro a v
  simp only [Module.End.mul_apply, Y_monomial]
  congr 1
  ac_rfl

/-- The Clifford operators square to the identity, including their reflections. -/
@[simp] theorem C_sq (i : Fin n) : C (R := R) i * C i = 1 := by
  apply ext
  intro a v
  simp only [Module.End.mul_apply, C_monomial, Module.End.one_apply]
  congr 1
  rw [mul_smul_comm, smul_smul, ← pow_add, ← two_mul, pow_mul]
  simp [← mul_assoc]

/-- Distinct Clifford operators anticommute. -/
theorem C_anticommute (i j : Fin n) (hij : i ≠ j) :
    C (R := R) i * C j = -(C j * C i) := by
  apply ext
  intro a v
  simp only [Module.End.mul_apply, LinearMap.neg_apply, C_monomial]
  change Finsupp.single a _ = -Finsupp.single a _
  rw [← Finsupp.single_neg]
  congr 1
  rw [mul_smul_comm, smul_smul, mul_smul_comm, smul_smul,
    ← mul_assoc, c_anticommute R n i j hij, neg_mul,
    smul_neg, ← mul_assoc]
  rw [mul_comm ((-1 : R) ^ a i)]

/-- A Clifford operator anticommutes with its own polynomial variable. -/
theorem C_Y_self (i : Fin n) : C (R := R) i * Y i = -(Y i * C i) := by
  apply ext
  intro a v
  simp only [Module.End.mul_apply, LinearMap.neg_apply, Y_monomial, C_monomial]
  simp [SkewPolynomial.expSingle, pow_succ, monomial]

/-- A Clifford operator commutes with every other polynomial variable. -/
theorem C_Y_of_ne (i j : Fin n) (hij : i ≠ j) :
    Commute (C (R := R) i) (Y j) := by
  apply ext
  intro a v
  simp [Module.End.mul_apply, SkewPolynomial.expSingle, Ne.symm hij]

/-- The dot images in KKT Theorem 3.13(a): `cᵢ yᵢ` at odd positions. -/
def X (p : Fin n → Bool) (i : Fin n) : Module.End R (Coeff R n) :=
  if p i then C i * Y i else Y i

private theorem mul_self_sq_of_anticomm {A : Type*} [Ring A]
    (c y : A) (hcc : c * c = 1) (hcy : c * y = -(y * c)) :
    (c * y) ^ 2 = -(y ^ 2) := by
  calc
    (c * y) ^ 2 = (-(y * c)) * (c * y) := by
      rw [pow_two]; exact congrArg (fun z => z * (c * y)) hcy
    _ = -(y * (c * c) * y) := by noncomm_ring
    _ = -(y ^ 2) := by rw [hcc]; simp [pow_two]

/-- Odd dot squares acquire precisely the minus sign in KKT (3.17). -/
theorem X_sq_odd (p : Fin n → Bool) (i : Fin n) (hi : p i = true) :
    X (R := R) p i ^ 2 = -(Y i ^ 2) := by
  simpa only [X, hi, ↓reduceIte] using
    mul_self_sq_of_anticomm (C (R := R) i) (Y (R := R) i)
      (C_sq (R := R) i) (C_Y_self (R := R) i)

/-- Dot images have precisely the mixed-parity supercommutation relation. -/
theorem X_supercommute (p : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) :
    X (R := R) p i * X p j =
      (if p i && p j then -1 else 1) * (X p j * X p i) := by
  have hee := Y_commute (R := R) i j
  have hoe := C_Y_of_ne (R := R) i j hij
  have heo := (C_Y_of_ne (R := R) j i hij.symm).symm
  cases hi : p i <;> cases hj : p j <;> simp only [X, hi, hj, Bool.and_self,
    Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte, one_mul]
  · exact hee.eq
  · exact (heo.mul_right hee).eq
  · exact (hoe.mul_left hee).eq
  · calc
      C i * Y i * (C j * Y j) = C (R := R) i * C j * (Y i * Y j) :=
        heo.mul_mul_mul_comm _ _
      _ = -(C (R := R) j * C i * (Y j * Y i)) := by
        rw [C_anticommute i j hij, hee.eq]
        rfl
      _ = -(C (R := R) j * Y j * (C i * Y i)) := by
        rw [hoe.mul_mul_mul_comm]

end OddMath.QuiverHecke.CliffordCoefficients
