import OddMath.SkewPolynomial

/-!
# Defining relations of the odd polynomial ring in the skew-polynomial model

Ellis-Khovanov-Lauda, arXiv:1111.1320v1, §2.1.1, (2.1) and (2.9): the ring of odd
polynomials is `ℤ⟨x_1, ..., x_n⟩ / (x_i x_j + x_j x_i = 0 for i ≠ j)`, with the sign
convention `x_i x_j = -x_j x_i`. This module checks that the finite-support model
`OddMath.SkewPolynomial` satisfies these relations and nothing more in degree two: generator
squares do not vanish (there is no exterior square-zero law).

Main results:
- `rel_anticommute`: `mul (generator i) (generator j) = -mul (generator j) (generator i)`
  for `i ≠ j`.
- `rel_sum`: the relation in ideal form, `mul gi gj + mul gj gi = 0`; this is the equation
  the evaluation map of `OddMath.PbwFactorization` must kill.
- `square_form` / `square_ne_zero`: a generator square is the doubled-exponent monomial with
  coefficient `1`, hence nonzero.
- `adequacy`: the conjunction of `rel_sum` and `square_ne_zero`.

The presented ring is `OddMath.PbwPresentation`, the comparison map is
`OddMath.PbwFactorization`, and the ring isomorphism is
`OddMath.Frontier.PbwEquivalence.presentedEquiv`.
-/

namespace OddMath.PbwModelRelations

/-- Distinct generators anticommute in the model. -/
theorem rel_anticommute {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
      (OddMath.SkewPolynomial.generator j)
      = -OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator j)
        (OddMath.SkewPolynomial.generator i) :=
  OddMath.SkewPolynomial.generator_anticommute i j h

/-- Relation-ideal form — the anticommutator sum vanishes in the model. -/
theorem rel_sum {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
      (OddMath.SkewPolynomial.generator j)
      + OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator j)
        (OddMath.SkewPolynomial.generator i) = 0 := by
  rw [rel_anticommute i j h]
  exact neg_add_cancel _

/-- A generator square is the doubled-exponent monomial with coefficient `1`. -/
theorem square_form {n : ℕ} (i : Fin n) :
    OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
      (OddMath.SkewPolynomial.generator i)
      = OddMath.SkewPolynomial.monomial
        (OddMath.SkewPolynomial.expSingle i + OddMath.SkewPolynomial.expSingle i) 1 :=
  OddMath.SkewPolynomial.generator_square i

/-- Generator squares do not vanish (no exterior square law is imposed). -/
theorem square_ne_zero {n : ℕ} (i : Fin n) :
    OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
      (OddMath.SkewPolynomial.generator i) ≠ 0 :=
  OddMath.SkewPolynomial.generator_square_ne_zero i

/-- Adequacy conjunction: the anticommutator sum vanishes and the square
does not. -/
theorem adequacy {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    (OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
      (OddMath.SkewPolynomial.generator j)
      + OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator j)
        (OddMath.SkewPolynomial.generator i) = 0)
    ∧ (OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
      (OddMath.SkewPolynomial.generator i) ≠ 0) :=
  ⟨rel_sum i j h, square_ne_zero i⟩

end OddMath.PbwModelRelations
