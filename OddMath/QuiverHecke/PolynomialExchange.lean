/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Polynomial
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Signed exchanges of mixed polynomial coefficients

The adjacent exchange in Hill–Wang, arXiv:1202.2769v2, Proposition 4.5,
equation (4.22): exchanging two odd colours negates every odd variable,
including those away from the exchanged positions. Normal ordering contributes
an additional sign on monomials. Positions here increase from left to right.
These exchanges are coefficient maps, not the parameter-weighted crossings of `Hn`.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.QuiverHecke.Polynomial
variable {R : Type*} [CommRing R] {n : ℕ}

/-- Reindexing by an adjacent transposition. -/
def exchangeIndex (i j : Fin n) (a : Fin n → ℕ) : Fin n → ℕ :=
  a ∘ Equiv.swap i j

@[simp] theorem exchangeIndex_add (i j : Fin n) (a b : Fin n → ℕ) :
    exchangeIndex i j (a + b) = exchangeIndex i j a + exchangeIndex i j b := rfl

@[simp] theorem exchangeIndex_twice (i j : Fin n) (a : Fin n → ℕ) :
    exchangeIndex i j (exchangeIndex i j a) = a := by
  funext k
  simp [exchangeIndex]

/-- Only the adjacent pair reverses order under an adjacent exchange. -/
private theorem exchange_order (i j k l : Fin n) (hij : i.val + 1 = j.val) :
    (if Equiv.swap i j l < Equiv.swap i j k then 1 else 0 : ℕ) +
        (if k = j ∧ l = i then 1 else 0) =
      (if l < k then 1 else 0) + (if k = i ∧ l = j then 1 else 0) := by
  have hne : i ≠ j := by intro h; subst j; omega
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp_all [Equiv.swap_apply_def] <;> split_ifs <;> omega

/-- The natural crossing count changes only at the exchanged adjacent pair. -/
theorem crossingCount_exchange (i j : Fin n) (hij : i.val + 1 = j.val)
    (a b : Fin n → ℕ) :
    OddMath.crossingCount (exchangeIndex i j a) (exchangeIndex i j b) + a j * b i =
      OddMath.crossingCount a b + a i * b j := by
  have hterm (k l : Fin n) :
      (if Equiv.swap i j l < Equiv.swap i j k then a k * b l else 0) +
          (if k = j ∧ l = i then a k * b l else 0) =
        (if l < k then a k * b l else 0) +
          (if k = i ∧ l = j then a k * b l else 0) := by
    have h := congrArg (fun z => z * (a k * b l)) (exchange_order i j k l hij)
    simpa only [Nat.add_mul, ite_mul, Nat.one_mul, Nat.zero_mul] using h
  have hs := congrArg (fun f : Fin n → Fin n → ℕ => ∑ k, ∑ l, f k l)
    (funext fun k => funext fun l => hterm k l)
  simp only [Finset.sum_add_distrib] at hs
  have hreindex : OddMath.crossingCount (exchangeIndex i j a) (exchangeIndex i j b) =
      ∑ k : Fin n, ∑ l : Fin n,
        if Equiv.swap i j l < Equiv.swap i j k then a k * b l else 0 := by
    simp only [OddMath.crossingCount, Finset.sum_filter, exchangeIndex, Function.comp_apply]
    conv_lhs => rw [← Equiv.sum_comp (Equiv.swap i j)]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Equiv.sum_comp (Equiv.swap i j)]
    simp
  rw [hreindex]
  simpa [OddMath.crossingCount, Finset.sum_filter, ite_and] using hs

/-- Parities of the exchanged word. -/
def exchangeParity (p : Fin n → Bool) (i j : Fin n) : Fin n → Bool :=
  p ∘ Equiv.swap i j

@[simp] theorem oddPart_exchange (p : Fin n → Bool) (i j : Fin n) (a : Fin n → ℕ) :
    oddPart (exchangeParity p i j) (exchangeIndex i j a) =
      exchangeIndex i j (oddPart p a) := rfl

/-- Sign exponent: normal ordering plus the odd-colour twist of every odd variable. -/
def exchangeCount (p : Fin n → Bool) (i j : Fin n) (a : Fin n → ℕ) : ℕ :=
  oddPart p a i * oddPart p a j +
    if p i = true ∧ p j = true then ∑ k, oddPart p a k else 0

/-- Scalar multiplying an ordered monomial under signed exchange. -/
def exchangeSign (p : Fin n → Bool) (i j : Fin n) (a : Fin n → ℕ) : R :=
  (-1 : R) ^ exchangeCount p i j a

private theorem exchangeCount_add (p : Fin n → Bool) (i j : Fin n) (a b : Fin n → ℕ) :
    exchangeCount p i j (a + b) = exchangeCount p i j a + exchangeCount p i j b +
      oddPart p a i * oddPart p b j + oddPart p a j * oddPart p b i := by
  simp only [exchangeCount, oddPart_add, Pi.add_apply, Finset.sum_add_distrib]
  split <;> ring

/-- Compatibility of signed exchange with the multiplication cocycle. -/
theorem exchangeSign_cocycle (p : Fin n → Bool) (i j : Fin n)
    (hij : i.val + 1 = j.val) (a b : Fin n → ℕ) :
    sign (R := R) p a b * exchangeSign p i j (a + b) =
      exchangeSign p i j a * exchangeSign p i j b *
        sign (exchangeParity p i j) (exchangeIndex i j a) (exchangeIndex i j b) := by
  have hc := crossingCount_exchange i j hij (oddPart p a) (oddPart p b)
  have he : OddMath.crossingCount (oddPart p a) (oddPart p b) + exchangeCount p i j (a + b) =
      exchangeCount p i j a + exchangeCount p i j b +
        OddMath.crossingCount (exchangeIndex i j (oddPart p a))
          (exchangeIndex i j (oddPart p b)) + 2 * (oddPart p a j * oddPart p b i) := by
    rw [exchangeCount_add]
    omega
  simp only [sign, exchangeSign, oddPart_exchange, ← pow_add]
  rw [he, pow_add, pow_mul]
  simp

/-- Signed exchange, extended linearly from the ordered monomials. -/
def exchange (p : Fin n → Bool) (i j : Fin n) :
    Polynomial R n p →ₗ[R] Polynomial R n (exchangeParity p i j) :=
  Finsupp.lsum R fun a => LinearMap.toSpanSingleton R _
    (monomial (exchangeParity p i j) (exchangeIndex i j a) (exchangeSign p i j a))

@[simp] theorem exchange_monomial (p : Fin n → Bool) (i j : Fin n)
    (a : Fin n → ℕ) (r : R) :
    exchange p i j (monomial p a r) =
      monomial (exchangeParity p i j) (exchangeIndex i j a) (r * exchangeSign p i j a) := by
  change (Finsupp.lsum R fun a => LinearMap.toSpanSingleton R _
    (Finsupp.single (exchangeIndex i j a) (exchangeSign p i j a))) (Finsupp.single a r) = _
  simp only [Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, Finsupp.smul_single, smul_eq_mul]
  rfl

/-- The mixed exchange is multiplicative over arbitrary commutative coefficients. -/
theorem exchange_mul (p : Fin n → Bool) (i j : Fin n) (hij : i.val + 1 = j.val)
    (f g : Polynomial R n p) : exchange p i j (f * g) = exchange p i j f * exchange p i j g := by
  induction f using induction_on p with
  | hz => simp
  | ha f₁ f₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]
  | hm a r =>
    induction g using induction_on p with
    | hz => simp
    | ha g₁ g₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
    | hm b s =>
      simp only [monomial_mul, exchange_monomial, exchangeIndex_add]
      congr 1
      calc
        r * s * sign p a b * exchangeSign p i j (a + b) =
            (r * s) * (sign p a b * exchangeSign p i j (a + b)) := by ring
        _ = (r * s) * (exchangeSign p i j a * exchangeSign p i j b *
            sign (exchangeParity p i j) (exchangeIndex i j a) (exchangeIndex i j b)) := by
          rw [exchangeSign_cocycle p i j hij]
        _ = _ := by ring

@[simp] theorem exchangeParity_twice (p : Fin n → Bool) (i j : Fin n) :
    exchangeParity (exchangeParity p i j) i j = p := by
  funext k
  simp [exchangeParity]

private theorem exchangeCount_exchange (p : Fin n → Bool) (i j : Fin n) (a : Fin n → ℕ) :
    exchangeCount (exchangeParity p i j) i j (exchangeIndex i j a) =
      exchangeCount p i j a := by
  simp only [exchangeCount, oddPart_exchange]
  simp only [exchangeIndex, exchangeParity, Function.comp_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [Equiv.sum_comp]
  congr 1
  · exact Nat.mul_comm _ _
  · congr 1
    exact propext and_comm

/-- Exchanging a pair twice is the identity, including the distant odd-variable signs. -/
@[simp] theorem exchange_twice (p : Fin n → Bool) (i j : Fin n)
    (f : Polynomial R n p) : exchange (exchangeParity p i j) i j (exchange p i j f) = f := by
  induction f using induction_on p with
  | hz => simp
  | ha f g hf hg => simp only [map_add, hf, hg]
  | hm a r =>
    simp only [exchange_monomial, exchangeIndex_twice, exchangeSign, exchangeCount_exchange]
    change Finsupp.single a (r * (-1 : R) ^ exchangeCount p i j a *
      (-1 : R) ^ exchangeCount p i j a) = Finsupp.single a r
    rw [_root_.mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp

@[simp] theorem exchange_one (p : Fin n → Bool) (i j : Fin n) :
    exchange (R := R) p i j 1 = 1 := by
  change exchange p i j (monomial p 0 1) = monomial (exchangeParity p i j) 0 1
  simp [exchangeSign, exchangeCount, exchangeIndex]

/-- The adjacent signed exchange is an algebra equivalence between the two wordwise
coefficient algebras. No field, characteristic or Cartan hypotheses are required. -/
def exchangeAlgEquiv (p : Fin n → Bool) (i j : Fin n) (hij : i.val + 1 = j.val) :
    Polynomial R n p ≃ₐ[R] Polynomial R n (exchangeParity p i j) where
  toFun := exchange p i j
  invFun := exchange (exchangeParity p i j) i j
  left_inv := exchange_twice p i j
  right_inv f := by
    induction f using induction_on (exchangeParity p i j) with
    | hz => simp
    | ha f g hf hg => simp only [map_add, hf, hg]
    | hm a r =>
      rw [exchange_monomial]
      change exchange p i j (monomial p (exchangeIndex i j a)
        (r * exchangeSign (exchangeParity p i j) i j a)) =
          monomial (exchangeParity p i j) a r
      rw [exchange_monomial, exchangeIndex_twice]
      change Finsupp.single a (r * exchangeSign (exchangeParity p i j) i j a *
        exchangeSign p i j (exchangeIndex i j a)) = Finsupp.single a r
      have hc := exchangeCount_exchange p i j (exchangeIndex i j a)
      rw [exchangeIndex_twice] at hc
      simp only [exchangeSign, ← hc]
      rw [_root_.mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
  map_mul' := exchange_mul p i j hij
  map_add' := (exchange p i j).map_add
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, exchange_one,
      Algebra.algebraMap_eq_smul_one]

private theorem oddPart_single (p : Fin n → Bool) (k : Fin n) :
    oddPart p (SkewPolynomial.expSingle k) =
      if p k then SkewPolynomial.expSingle k else 0 := by
  funext l
  by_cases h : k = l
  · subst l; cases hpk : p k <;> simp [oddPart, SkewPolynomial.expSingle, hpk]
  · cases p k <;> simp [oddPart, SkewPolynomial.expSingle, h]

private theorem exchangeIndex_single (i j k : Fin n) :
    exchangeIndex i j (SkewPolynomial.expSingle k) =
      SkewPolynomial.expSingle (Equiv.swap i j k) := by
  funext l
  have he : k = Equiv.swap i j l ↔ Equiv.swap i j k = l := by
    constructor <;> intro h
    · rw [h]; simp
    · rw [← h]; simp
  simp only [exchangeIndex, Function.comp_apply, SkewPolynomial.expSingle, he]

private theorem exchangeSign_single (p : Fin n → Bool) (i j k : Fin n) (hij : i ≠ j) :
    exchangeSign (R := R) p i j (SkewPolynomial.expSingle k) =
      if p i = true ∧ p j = true ∧ p k = true then -1 else 1 := by
  simp only [exchangeSign, exchangeCount, oddPart_single]
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    cases hpi : p i <;> cases hpj : p j <;> cases hpk : p k <;>
    simp_all [SkewPolynomial.expSingle]

/-- HW (4.22): an odd–odd exchange negates every odd variable, not just its two strands. -/
@[simp] theorem exchange_X (p : Fin n → Bool) (i j k : Fin n) (hij : i ≠ j) :
    exchange (R := R) p i j (X p k) =
      (if p i = true ∧ p j = true ∧ p k = true then (-1 : R) else 1) •
        X (exchangeParity p i j) (Equiv.swap i j k) := by
  simp only [X, exchange_monomial, exchangeIndex_single, exchangeSign_single p i j k hij,
    smul_monomial]
  congr 1
  ring

/-- Dot transport under adjacent signed exchange, on arbitrary mixed polynomials. -/
theorem exchange_X_mul (p : Fin n → Bool) (i j k : Fin n) (hij : i.val + 1 = j.val)
    (f : Polynomial R n p) : exchange p i j (X p k * f) =
      (if p i = true ∧ p j = true ∧ p k = true then (-1 : R) else 1) •
        (X (exchangeParity p i j) (Equiv.swap i j k) * exchange p i j f) := by
  have hne : i ≠ j := by intro h; subst j; omega
  rw [exchange_mul p i j hij, exchange_X p i j k hne, smul_mul_assoc]

end OddMath.QuiverHecke.Polynomial
