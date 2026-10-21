import OddMath.PbwModelRelations
import OddMath.PbwPresentation
import OddMath.PbwFactorization

/-!
# Monomial spanning in the skew-polynomial model

Every `f : SkewPolynomial n` is a finite `ℤ`-sum of monomials (exponent vectors).
Ordered generator pairs multiply to a monomial with sign `+1` and reversed pairs with sign
`-1` (via `skewSign_expSingle`); single-generator powers are monomials at every degree. The
generator power `^` comes from the `Ring` instance of `OddMath.PbwFactorization`.

Main results:
- `self_cross`: a unit vector has no self-crossing.
- `ordered_sign`: the unit-vector sign is `+1` on ordered pairs.
- `ordered_pair`: ordered generator pairs are monomials with coefficient `1`.
- `reversed_pair`: reversed generator pairs are monomials with coefficient `-1`.
- `reduce_pair`: every reversed pair reduces to the negated ordered monomial (the degree-two
  normal-form rewrite).
- `monomial_smul`: every monomial is a `ℤ`-multiple of a unit monomial.
- `span_expand`: every `f` is the sum of its monomials.
- `pow_cross` / `pow_sign`: scaled unit vectors never self-cross.
- `pow_form`: single-generator powers are scaled-exponent monomials.
- `spanning`: the conjunction of `span_expand`, `ordered_pair` and `pow_form`.

Every exponent vector is realized by an ordered generator word in
`OddMath.Frontier.PbwRealization`.
-/

namespace OddMath.PbwSpanning

open OddMath.SkewPolynomial

/-- A unit vector has no self-crossing (equal indices do not cross). -/
theorem self_cross (n : ℕ) (i : Fin n) :
    OddMath.crossingCount (expSingle i) (expSingle i) = 0 := by
  rw [crossingCount_expSingle, ite_eq_right (lt_irrefl _)]

/-- The unit-vector sign is `+1` on ordered pairs. -/
theorem ordered_sign (n : ℕ) (i j : Fin n) (h : i ≤ j) :
    OddMath.skewSign (expSingle i) (expSingle j) = 1 := by
  rw [skewSign_expSingle, ite_eq_right (not_lt.mpr h)]

/-- Ordered generator pairs are ordered monomials with coeff `1`. -/
theorem ordered_pair (n : ℕ) (i j : Fin n) (h : i ≤ j) :
    OddMath.SkewPolynomial.mul (generator i) (generator j)
      = monomial (expSingle i + expSingle j) 1 := by
  rw [mul_generator, ordered_sign n i j h]

/-- Reversed generator pairs are monomials with coeff `-1`. -/
theorem reversed_pair (n : ℕ) (i j : Fin n) (h : j < i) :
    OddMath.SkewPolynomial.mul (generator i) (generator j)
      = monomial (expSingle i + expSingle j) (-1) := by
  rw [mul_generator, skewSign_expSingle, ite_eq_left h]

/-- Every reversed word reduces to the negated ordered monomial (the
degree-two normal-form rewrite, sign-correct by `skewSign`). -/
theorem reduce_pair (n : ℕ) (i j : Fin n) (h : j < i) :
    OddMath.SkewPolynomial.mul (generator i) (generator j)
      = -monomial (expSingle j + expSingle i) 1 := by
  rw [reversed_pair n i j h, add_comm (expSingle i) (expSingle j), monomial_neg]

/-- Every monomial is a `ℤ`-multiple of a unit monomial. -/
theorem monomial_smul (n : ℕ) (a : Fin n → ℕ) (c : ℤ) :
    monomial a c = c • monomial a 1 :=
  (Finsupp.smul_single_one a c).symm

/-- Every `f` is its own finite monomial sum (spanning existence). -/
theorem span_expand (n : ℕ) (f : OddMath.SkewPolynomial.SkewPolynomial n) :
    f.sum (fun a r => monomial a r) = f :=
  Finsupp.sum_single f

/-- Scaled unit vectors never self-cross. -/
theorem pow_cross (n : ℕ) (i : Fin n) (k : ℕ) :
    OddMath.crossingCount (k • expSingle i) (expSingle i) = 0 := by
  induction k with
  | zero =>
      rw [zero_smul]
      exact crossingCount_zero_left _
  | succ k ih =>
      have hexp : (k + 1) • expSingle i = k • expSingle i + expSingle i := by
        rw [add_smul, one_smul]
      rw [hexp, OddMath.crossingCount_add_left, ih, self_cross n i, add_zero]

/-- The same-generator power sign is `+1` at every degree. -/
theorem pow_sign (n : ℕ) (i : Fin n) (k : ℕ) :
    OddMath.skewSign (k • expSingle i) (expSingle i) = 1 := by
  show (-1 : ℤ) ^ OddMath.crossingCount (k • expSingle i) (expSingle i) = 1
  rw [pow_cross n i k, pow_zero]

/-- Single-generator powers are scaled-exponent monomials. -/
theorem pow_form (n : ℕ) (i : Fin n) (k : ℕ) :
    (generator i ^ k) = monomial (k • expSingle i) 1 := by
  induction k with
  | zero =>
      rw [pow_zero, zero_smul]
      rfl
  | succ k ih =>
      have hexp : k • expSingle i + expSingle i = (k + 1) • expSingle i := by
        rw [add_smul, one_smul]
      calc generator i ^ (k + 1)
          = generator i ^ k * generator i := pow_succ _ _
        _ = OddMath.SkewPolynomial.mul (generator i ^ k) (generator i) := rfl
        _ = OddMath.SkewPolynomial.mul (monomial (k • expSingle i) 1)
              (monomial (expSingle i) 1) := by rw [ih]; rfl
        _ = monomial (k • expSingle i + expSingle i)
              (1 * 1 * OddMath.skewSign (k • expSingle i) (expSingle i)) := by
            rw [mul_monomial]
        _ = monomial (k • expSingle i + expSingle i) 1 := by
            rw [pow_sign n i k, _root_.mul_one, _root_.one_mul]
        _ = monomial ((k + 1) • expSingle i) 1 := by rw [hexp]

/-- Adequacy conjunction: monomial expansion, ordered-pair form and
power form. -/
theorem spanning (n : ℕ) (f : OddMath.SkewPolynomial.SkewPolynomial n)
    (i j : Fin n) (h : i ≤ j) (k : ℕ) (l : Fin n) :
    (f.sum (fun a r => monomial a r) = f)
    ∧ (OddMath.SkewPolynomial.mul (generator i) (generator j)
        = monomial (expSingle i + expSingle j) 1)
    ∧ ((generator l ^ k) = monomial (k • expSingle l) 1) :=
  ⟨span_expand n f, ordered_pair n i j h, pow_form n l k⟩

end OddMath.PbwSpanning
