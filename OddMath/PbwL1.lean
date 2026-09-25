import OddMath.SkewPolynomial

/-!
# PBW lemma L1: relations adequacy in the finite-support model

Roadmap: an unpublished note, §4,
lemma L1 (R0). This is the model side of generator-relations adequacy for the
quotient/PBW correspondence, proved over the already-constructed
`OddMath.SkewPolynomial` model (no new definitions, no quotient object).

What this module proves (sorry-free):
- `rel_anticommute`: distinct generators anticommute,
  `mul (generator i) (generator j) = -mul (generator j) (generator i)` for
  `i ≠ j` (the EKL §2.1.1 relations (2.1)/(2.9), first half, instantiated in
  the model; locked convention the sign convention: `x_i x_j = -x_j x_i`).
- `rel_sum`: the relation-ideal form `mul gi gj + mul gj gi = 0` (the shape
  the presented-algebra side L2 imposes by construction on its quotient
  generators `q_i`; this is the exact equation the L3 evaluation map must
  kill to factor through the relation ideal).
- `square_form` / `square_ne_zero`: a generator square is the
  doubled-exponent monomial with coefficient `1`, hence nonzero — the model
  imposes NO exterior square-zero law (roadmap §5 explicit non-goal
  `x_i^2 = 0` is false here).
- `adequacy`: the conjunction both successors need: the anticommutator sum
  vanishes AND the square does not.

Scope (NOT this module): the presented object `P n`, quotient map `π`, word
evaluation `eval`, factorization `Φ` (L2/L3); spanning/normal-form existence
(L4); linear independence (L5); the isomorphism/PBW corollary (L6). Finite
fixtures in `OddMath/Tests/PbwL1Fixtures.lean` are development aids
(`SUPPORTED_LOW_DEGREE` at most), never a proof of the correspondence.
-/

namespace OddMath.PbwL1

/-- L1a: distinct generators anticommute in the model. -/
theorem rel_anticommute {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
      (OddMath.SkewPolynomial.generator j)
      = -OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator j)
        (OddMath.SkewPolynomial.generator i) :=
  OddMath.SkewPolynomial.generator_anticommute i j h

/-- L1b: relation-ideal form — the anticommutator sum vanishes in the model. -/
theorem rel_sum {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
      (OddMath.SkewPolynomial.generator j)
      + OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator j)
        (OddMath.SkewPolynomial.generator i) = 0 := by
  rw [rel_anticommute i j h]
  exact neg_add_cancel _

/-- L1c: a generator square is the doubled-exponent monomial with coefficient `1`. -/
theorem square_form {n : ℕ} (i : Fin n) :
    OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
      (OddMath.SkewPolynomial.generator i)
      = OddMath.SkewPolynomial.monomial
        (OddMath.SkewPolynomial.expSingle i + OddMath.SkewPolynomial.expSingle i) 1 :=
  OddMath.SkewPolynomial.generator_square i

/-- L1d: generator squares do not vanish (no exterior square law is imposed). -/
theorem square_ne_zero {n : ℕ} (i : Fin n) :
    OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
      (OddMath.SkewPolynomial.generator i) ≠ 0 :=
  OddMath.SkewPolynomial.generator_square_ne_zero i

/-- L1 adequacy conjunction: the anticommutator sum vanishes and the square
does not — the exact model-side input the L3 factorization needs. -/
theorem adequacy {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    (OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
      (OddMath.SkewPolynomial.generator j)
      + OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator j)
        (OddMath.SkewPolynomial.generator i) = 0)
    ∧ (OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.generator i)
      (OddMath.SkewPolynomial.generator i) ≠ 0) :=
  ⟨rel_sum i j h, square_ne_zero i⟩

end OddMath.PbwL1
