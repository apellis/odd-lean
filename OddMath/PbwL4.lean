import OddMath.PbwL1
import OddMath.PbwL2
import OddMath.PbwL3

/-!
# PBW lemma L4: spanning / normal-form existence in the model

Roadmap: an unpublished note, §4,
lemma L4 (R0). This is the model-side spanning direction of the quotient/PBW
correspondence: every `f : SkewPolynomial n` is a finite `ℤ`-sum of monomials
(the exponent-vector normal forms), ordered generator pairs multiply with
`+1` sign, reversed pairs with `-1` sign (the reorder sign is
`skewSign`-correct via `skewSign_expSingle`), and single-generator powers are
scaled-exponent monomials at arbitrary degree.

No new definitions (R0): only theorems over the verified `SkewPolynomial` +
`PbwL2` + `PbwL3` interface (the `PbwL3` `Ring` instance supplies the
generator power `^`). No quotient content is changed (that is L2/L3, built
on, not redone).

What this module proves (sorry-free):
- `self_cross`: a unit vector has no self-crossing.
- `ordered_sign`: the unit-vector sign is `+1` on ordered pairs.
- `ordered_pair`: ordered generator pairs are ordered monomials, coeff `1`.
- `reversed_pair`: reversed generator pairs are monomials, coeff `-1`.
- `reduce_pair`: every reversed word reduces to the negated ordered monomial
  (the degree-two normal-form rewrite).
- `monomial_smul`: every monomial is a `ℤ`-multiple of a unit monomial.
- `span_expand`: every `f` is its own finite monomial sum (existence).
- `pow_cross` / `pow_sign`: scaled unit vectors never self-cross.
- `pow_form`: single-generator powers are scaled-exponent monomials.
- `spanning`: adequacy conjunction — expansion AND ordered-pair form AND
  power form (the exact input L6 needs for surjectivity).

Scope (NOT this module): linear independence (L5); the isomorphism/PBW
corollary (L6). The full arbitrary-degree ordered-word realization (every
exponent vector as an explicit ordered generator list product) is future
work: see the remainder note in the unpublished development notes. Finite fixtures in
`OddMath/Tests/PbwL4Fixtures.lean` are development aids
(`SUPPORTED_LOW_DEGREE` at most), never a proof of the correspondence.
-/

namespace OddMath.PbwL4

open OddMath.SkewPolynomial

/-- L4a: a unit vector has no self-crossing (equal indices do not cross). -/
theorem self_cross (n : ℕ) (i : Fin n) :
    OddMath.crossingCount (expSingle i) (expSingle i) = 0 := by
  rw [crossingCount_expSingle, if_neg (lt_irrefl _)]

/-- L4b: the unit-vector sign is `+1` on ordered pairs. -/
theorem ordered_sign (n : ℕ) (i j : Fin n) (h : i ≤ j) :
    OddMath.skewSign (expSingle i) (expSingle j) = 1 := by
  rw [skewSign_expSingle, if_neg (not_lt.mpr h)]

/-- L4c: ordered generator pairs are ordered monomials with coeff `1`. -/
theorem ordered_pair (n : ℕ) (i j : Fin n) (h : i ≤ j) :
    OddMath.SkewPolynomial.mul (generator i) (generator j)
      = monomial (expSingle i + expSingle j) 1 := by
  rw [mul_generator, ordered_sign n i j h]

/-- L4d: reversed generator pairs are monomials with coeff `-1`. -/
theorem reversed_pair (n : ℕ) (i j : Fin n) (h : j < i) :
    OddMath.SkewPolynomial.mul (generator i) (generator j)
      = monomial (expSingle i + expSingle j) (-1) := by
  rw [mul_generator, skewSign_expSingle, if_pos h]

/-- L4e: every reversed word reduces to the negated ordered monomial (the
degree-two normal-form rewrite, sign-correct by `skewSign`). -/
theorem reduce_pair (n : ℕ) (i j : Fin n) (h : j < i) :
    OddMath.SkewPolynomial.mul (generator i) (generator j)
      = -monomial (expSingle j + expSingle i) 1 := by
  rw [reversed_pair n i j h, add_comm (expSingle i) (expSingle j), monomial_neg]

/-- L4f: every monomial is a `ℤ`-multiple of a unit monomial. -/
theorem monomial_smul (n : ℕ) (a : Fin n → ℕ) (c : ℤ) :
    monomial a c = c • monomial a 1 :=
  (Finsupp.smul_single_one a c).symm

/-- L4g: every `f` is its own finite monomial sum (spanning existence). -/
theorem span_expand (n : ℕ) (f : OddMath.SkewPolynomial.SkewPolynomial n) :
    f.sum (fun a r => monomial a r) = f :=
  Finsupp.sum_single f

/-- L4h: scaled unit vectors never self-cross. -/
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

/-- L4i: the same-generator power sign is `+1` at every degree. -/
theorem pow_sign (n : ℕ) (i : Fin n) (k : ℕ) :
    OddMath.skewSign (k • expSingle i) (expSingle i) = 1 := by
  show (-1 : ℤ) ^ OddMath.crossingCount (k • expSingle i) (expSingle i) = 1
  rw [pow_cross n i k, pow_zero]

/-- L4j: single-generator powers are scaled-exponent monomials. -/
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

/-- L4 adequacy conjunction: monomial expansion AND ordered-pair form AND
power form — the exact spanning input L6 needs for surjectivity. -/
theorem spanning (n : ℕ) (f : OddMath.SkewPolynomial.SkewPolynomial n)
    (i j : Fin n) (h : i ≤ j) (k : ℕ) (l : Fin n) :
    (f.sum (fun a r => monomial a r) = f)
    ∧ (OddMath.SkewPolynomial.mul (generator i) (generator j)
        = monomial (expSingle i + expSingle j) 1)
    ∧ ((generator l ^ k) = monomial (k • expSingle l) 1) :=
  ⟨span_expand n f, ordered_pair n i j h, pow_form n l k⟩

end OddMath.PbwL4
