/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SkewPolynomial
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Mixed-parity polynomial coefficients

The polynomial coefficient module for Hill–Wang, arXiv:1202.2769v2,
Proposition 4.5, and Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2, §3.1.
Only distinct odd variables anticommute. An odd variable has arbitrary
nonnegative powers; this is not an exterior algebra.

Monomials are ordered by increasing strand index. The coefficient ring is
commutative and purely even. This module constructs the coefficient algebra,
not the crossing action or the PBW basis of the quiver Hecke algebra.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.QuiverHecke

/-- Ordered polynomial coefficients for the parity assignment `p`. -/
def Polynomial (R : Type*) (n : ℕ) (_p : Fin n → Bool) [CommRing R] :=
  (Fin n → ℕ) →₀ R

namespace Polynomial
variable {R : Type*} [CommRing R] {n : ℕ} (p : Fin n → Bool)

instance : AddCommGroup (Polynomial R n p) :=
  inferInstanceAs (AddCommGroup ((Fin n → ℕ) →₀ R))
instance : Module R (Polynomial R n p) :=
  inferInstanceAs (Module R ((Fin n → ℕ) →₀ R))

/-- Exponents at odd positions, used in the normal-ordering sign. -/
def oddPart (a : Fin n → ℕ) : Fin n → ℕ := fun i => if p i then a i else 0

@[simp] theorem oddPart_add (a b : Fin n → ℕ) :
    oddPart p (a + b) = oddPart p a + oddPart p b := by
  funext i
  simp only [oddPart, Pi.add_apply]
  split <;> simp

@[simp] theorem oddPart_zero : oddPart p 0 = 0 := by
  funext i
  simp [oddPart]

/-- The Koszul sign of normal ordering, with no crossing of equal positions. -/
def sign (a b : Fin n → ℕ) : R :=
  (-1 : R) ^ OddMath.crossingCount (oddPart p a) (oddPart p b)

@[simp] theorem sign_zero_left (a : Fin n → ℕ) : sign (R := R) p 0 a = 1 := by
  simp [sign, OddMath.crossingCount]

@[simp] theorem sign_zero_right (a : Fin n → ℕ) : sign (R := R) p a 0 = 1 := by
  simp [sign, OddMath.crossingCount]

/-- The normal-ordering sign satisfies the associativity cocycle. -/
theorem sign_cocycle (a b c : Fin n → ℕ) :
    sign (R := R) p a b * sign p (a + b) c =
      sign p b c * sign p a (b + c) := by
  simp only [sign, oddPart_add, ← pow_add]
  rw [OddMath.crossingCount_cocycle]

/-- A coefficient on a single ordered monomial. -/
def monomial (a : Fin n → ℕ) (r : R) : Polynomial R n p := Finsupp.single a r

@[simp] theorem monomial_zero (a : Fin n → ℕ) : monomial p a (0 : R) = 0 :=
  Finsupp.single_zero _

@[simp] theorem monomial_add (a : Fin n → ℕ) (r s : R) :
    monomial p a (r + s) = monomial p a r + monomial p a s :=
  Finsupp.single_add _ _ _

@[simp] theorem smul_monomial (a : Fin n → ℕ) (r s : R) :
    r • monomial p a s = monomial p a (r * s) := Finsupp.smul_single ..

/-- Bilinear extension of the ordered-monomial multiplication table. -/
private def mulCoefficients : ((Fin n → ℕ) →₀ R) →ₗ[R]
    ((Fin n → ℕ) →₀ R) →ₗ[R] ((Fin n → ℕ) →₀ R) :=
  Finsupp.lsum R fun a => LinearMap.toSpanSingleton R _
    (Finsupp.lsum R fun b => LinearMap.toSpanSingleton R _
      (Finsupp.single (a + b) (sign p a b)))

/-- Bilinear multiplication on the mixed-parity coefficient module. -/
def mulLinear : Polynomial R n p →ₗ[R] Polynomial R n p →ₗ[R] Polynomial R n p :=
  mulCoefficients p

instance : Mul (Polynomial R n p) := ⟨fun f g => mulLinear p f g⟩
instance : One (Polynomial R n p) := ⟨monomial p 0 1⟩

/-- Multiplication is the Koszul normal-ordering rule on monomials. -/
@[simp] theorem monomial_mul (a b : Fin n → ℕ) (r s : R) :
    monomial p a r * monomial p b s =
      monomial p (a + b) (r * s * sign p a b) := by
  change mulCoefficients p (Finsupp.single a r) (Finsupp.single b s) =
    Finsupp.single (a + b) (r * s * sign p a b)
  simp only [mulCoefficients, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    LinearMap.smul_apply, Finsupp.smul_single, smul_eq_mul, _root_.mul_assoc]

@[simp] theorem zero_mul (f : Polynomial R n p) : 0 * f = 0 := by
  change mulLinear p 0 f = 0
  rw [map_zero, LinearMap.zero_apply]

@[simp] theorem mul_zero (f : Polynomial R n p) : f * 0 = 0 := (mulLinear p f).map_zero

theorem add_mul (f g h : Polynomial R n p) : (f + g) * h = f * h + g * h := by
  change mulLinear p (f + g) h = _
  rw [map_add, LinearMap.add_apply]
  rfl

theorem mul_add (f g h : Polynomial R n p) : f * (g + h) = f * g + f * h :=
  (mulLinear p f).map_add g h

/-- Induction on finite sums of ordered monomials. -/
@[elab_as_elim] theorem induction_on {P : Polynomial R n p → Prop}
    (f : Polynomial R n p) (hz : P 0)
    (ha : ∀ f g, P f → P g → P (f + g))
    (hm : ∀ a r, P (monomial p a r)) : P f := by
  exact Finsupp.induction f hz (fun a r f _ _ hf => ha _ _ (hm a r) hf)

theorem mul_assoc (f g h : Polynomial R n p) : (f * g) * h = f * (g * h) := by
  induction f using induction_on p with
  | hz => simp
  | ha f₁ f₂ h₁ h₂ => simp only [add_mul, h₁, h₂]
  | hm a r =>
    induction g using induction_on p with
    | hz => simp
    | ha g₁ g₂ h₁ h₂ => simp only [mul_add, add_mul, h₁, h₂]
    | hm b s =>
      induction h using induction_on p with
      | hz => simp
      | ha h₁ h₂ ih₁ ih₂ => simp only [mul_add, ih₁, ih₂]
      | hm c t =>
        simp only [monomial_mul, add_assoc]
        congr 1
        calc
          r * s * sign p a b * t * sign p (a + b) c =
              (r * s * t) * (sign p a b * sign p (a + b) c) := by ac_rfl
          _ = (r * s * t) * (sign p b c * sign p a (b + c)) := by
            rw [sign_cocycle]
          _ = r * (s * t * sign p b c) * sign p a (b + c) := by ac_rfl

theorem one_mul (f : Polynomial R n p) : 1 * f = f := by
  induction f using induction_on p with
  | hz => simp
  | ha f g hf hg => rw [mul_add, hf, hg]
  | hm a r => change monomial p 0 1 * monomial p a r = _; simp

theorem mul_one (f : Polynomial R n p) : f * 1 = f := by
  induction f using induction_on p with
  | hz => simp
  | ha f g hf hg => rw [add_mul, hf, hg]
  | hm a r => change monomial p a r * monomial p 0 1 = _; simp

instance : Ring (Polynomial R n p) where
  left_distrib := mul_add p
  right_distrib := add_mul p
  zero_mul := zero_mul p
  mul_zero := mul_zero p
  mul_assoc := mul_assoc p
  one_mul := one_mul p
  mul_one := mul_one p

/-- The independent ordered monomials form the coefficient-module basis.
This is not yet a basis of the quiver Hecke algebra. -/
def monomialBasis : Module.Basis (Fin n → ℕ) R (Polynomial R n p) :=
  Finsupp.basisSingleOne

@[simp] theorem monomialBasis_apply (a : Fin n → ℕ) :
    monomialBasis (R := R) p a = monomial p a 1 := rfl

/-- Scalars act centrally, as required for purely even coefficients. -/
instance : Algebra R (Polynomial R n p) :=
  Algebra.ofModule
    (fun r f g => by
      change mulLinear p (r • f) g = r • mulLinear p f g
      rw [map_smul, LinearMap.smul_apply])
    (fun r f g => (mulLinear p f).map_smul r g)

/-- The variable at a strand position. -/
def X (i : Fin n) : Polynomial R n p := monomial p (SkewPolynomial.expSingle i) 1

private theorem oddPart_expSingle (i : Fin n) :
    oddPart p (SkewPolynomial.expSingle i) =
      if p i then SkewPolynomial.expSingle i else 0 := by
  funext j
  by_cases h : i = j
  · subst j; cases hpi : p i <;> simp [oddPart, SkewPolynomial.expSingle, hpi]
  · cases p i <;> simp [oddPart, SkewPolynomial.expSingle, h]

private theorem sign_expSingle (i j : Fin n) :
    sign (R := R) p (SkewPolynomial.expSingle i) (SkewPolynomial.expSingle j) =
      if p i = true ∧ p j = true ∧ j < i then -1 else 1 := by
  simp only [sign, oddPart_expSingle]
  cases p i <;> cases p j <;>
    simp [SkewPolynomial.crossingCount_zero_left,
      SkewPolynomial.crossingCount_zero_right, SkewPolynomial.crossingCount_expSingle]

/-- The explicit two-variable normal-ordering formula. -/
theorem X_mul_X (i j : Fin n) :
    X (R := R) p i * X p j = monomial p
      (SkewPolynomial.expSingle i + SkewPolynomial.expSingle j)
      (if p i = true ∧ p j = true ∧ j < i then -1 else 1) := by
  simp [X, sign_expSingle]

/-- Distinct odd variables anticommute; all other distinct pairs commute. -/
theorem X_mul_X_swap (i j : Fin n) (h : i ≠ j) :
    X (R := R) p i * X p j =
      (if p i = true ∧ p j = true then (-1 : R) else 1) • (X p j * X p i) := by
  rw [X_mul_X, X_mul_X, smul_monomial, add_comm (SkewPolynomial.expSingle j)]
  congr 1
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hn := not_lt_of_gt hlt
    cases p i <;> cases p j <;> simp [hlt, hn]
  · have hn := not_lt_of_gt hgt
    cases p i <;> cases p j <;> simp [hgt, hn]

/-- Odd squares remain ordinary monomials, rather than exterior zeros. -/
theorem X_sq (i : Fin n) :
    X (R := R) p i ^ 2 =
      monomial p (SkewPolynomial.expSingle i + SkewPolynomial.expSingle i) 1 := by
  rw [pow_two, X_mul_X]
  simp

/-- No variable square vanishes over a nontrivial coefficient ring. -/
theorem X_sq_ne_zero [Nontrivial R] (i : Fin n) : X (R := R) p i ^ 2 ≠ 0 := by
  rw [X_sq]
  exact Finsupp.single_ne_zero.mpr one_ne_zero

/-- Squaring a normal-ordering sign removes it, in every characteristic. -/
theorem sign_sq (a b : Fin n → ℕ) : sign (R := R) p a b ^ 2 = 1 := by
  rw [sign, ← pow_mul, Nat.mul_comm, pow_mul]
  simp

@[simp] theorem sign_double_left (a b : Fin n → ℕ) :
    sign (R := R) p (a + a) b = 1 := by
  simp only [sign, oddPart_add, OddMath.crossingCount_add_left, pow_add]
  exact (pow_two _).symm.trans (sign_sq p a b)

@[simp] theorem sign_double_right (a b : Fin n → ℕ) :
    sign (R := R) p a (b + b) = 1 := by
  simp only [sign, oddPart_add, OddMath.crossingCount_add_right, pow_add]
  exact (pow_two _).symm.trans (sign_sq p a b)

/-- Monomials with all exponents even commute with every polynomial.
This is a coefficient-algebra statement, not centrality across crossings. -/
theorem double_monomial_commute (a : Fin n → ℕ) (r : R) (f : Polynomial R n p) :
    Commute (monomial p (a + a) r) f := by
  change monomial p (a + a) r * f = f * monomial p (a + a) r
  induction f using induction_on p with
  | hz => simp
  | ha f g hf hg => simp only [mul_add, add_mul, hf, hg]
  | hm b s => simp [monomial_mul, add_comm (a + a), _root_.mul_comm r s]

/-- In particular every variable square is central in the coefficient algebra. -/
theorem X_sq_commute (i : Fin n) (f : Polynomial R n p) : Commute (X p i ^ 2) f := by
  rw [X_sq]
  exact double_monomial_commute p _ 1 f

/-- Left multiplication on the coefficient module. This is the dot part of
HW Proposition 4.5, not yet an action of the crossing generators. -/
def leftRegular : Polynomial R n p →ₐ[R] Module.End R (Polynomial R n p) :=
  Algebra.lmul R (Polynomial R n p)

/-- The polynomial coefficient algebra acts faithfully on itself. -/
theorem leftRegular_injective : Function.Injective (leftRegular (R := R) p) := by
  intro f g h
  have he := congrArg (fun F : Module.End R (Polynomial R n p) => F 1) h
  simpa [leftRegular] using he

end Polynomial
end OddMath.QuiverHecke
