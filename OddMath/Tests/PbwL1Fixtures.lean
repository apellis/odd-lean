import OddMath.PbwL1

/-! Hand-derived PBW L1 fixtures, written BEFORE the module exists (TDD red step).

Roadmap: an unpublished note, §4.
L1 (R0) is relations adequacy in the model: distinct generators anticommute
(`x_i x_j = -x_j x_i`, `i ≠ j`; EKL arXiv:1111.1320v1 §2.1.1, (2.1)/(2.9)
via `diagram-relations/relations.json` R-2.01/R-2.09A; locked by
the sign convention) and generator squares do NOT vanish (no exterior
square law is imposed).

Values below are hand-derived from the locked conventions BEFORE any Lean is
written:
- F1 rank-two pair (0,1): anticommute instance.
- F2 rank-two pair (0,1): relation-ideal form (anticommutator sum = 0).
- F3 rank-two square (0,0): nonvanishing.
- F4 rank-one square: nonvanishing (the `n = 1` edge case has no pairs).
- F5 rank-three outer pair (0,2): anticommute + sum instances.
- F6/F7 rank-two coordinates: ordered product at ![1,1] is 1, reversed is -1
  (grounding probes inherited from `SkewPolynomialFixtures.lean`).
- F8 adequacy conjunction on the rank-two pair.
This file MUST fail to elaborate until `OddMath.PbwL1` exists.
-/

namespace OddMath.PbwL1.Tests

/-- F1: the rank-two distinct pair anticommutes. -/
example : OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (0 : Fin 2))
    (OddMath.SkewPolynomial.generator 1)
  = -OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (1 : Fin 2))
    (OddMath.SkewPolynomial.generator 0) :=
  OddMath.PbwL1.rel_anticommute 0 1 (by decide)

/-- F2: relation-ideal form on the rank-two pair: `x_0 x_1 + x_1 x_0 = 0`. -/
example : OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (0 : Fin 2))
    (OddMath.SkewPolynomial.generator 1)
  + OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (1 : Fin 2))
    (OddMath.SkewPolynomial.generator 0) = 0 :=
  OddMath.PbwL1.rel_sum 0 1 (by decide)

/-- F3: the rank-two generator square does not vanish. -/
example : OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (0 : Fin 2))
    (OddMath.SkewPolynomial.generator 0) ≠ 0 :=
  OddMath.PbwL1.square_ne_zero 0

/-- F4: the rank-one generator square does not vanish. -/
example : OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (0 : Fin 1))
    (OddMath.SkewPolynomial.generator 0) ≠ 0 :=
  OddMath.PbwL1.square_ne_zero 0

/-- F5a: the rank-three outer pair anticommutes. -/
example : OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (0 : Fin 3))
    (OddMath.SkewPolynomial.generator 2)
  = -OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (2 : Fin 3))
    (OddMath.SkewPolynomial.generator 0) :=
  OddMath.PbwL1.rel_anticommute 0 2 (by decide)

/-- F5b: relation-ideal form on the rank-three outer pair. -/
example : OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (0 : Fin 3))
    (OddMath.SkewPolynomial.generator 2)
  + OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (2 : Fin 3))
    (OddMath.SkewPolynomial.generator 0) = 0 :=
  OddMath.PbwL1.rel_sum 0 2 (by decide)

/-- F6: ordered rank-two product coordinate is `1`. -/
example : (OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (0 : Fin 2))
    (OddMath.SkewPolynomial.generator 1)) ![1, 1] = 1 :=
  OddMath.SkewPolynomial.ordered_rank_two_coordinate

/-- F7: reversed rank-two product coordinate is `-1`. -/
example : (OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (1 : Fin 2))
    (OddMath.SkewPolynomial.generator 0)) ![1, 1] = -1 :=
  OddMath.SkewPolynomial.reversed_rank_two_coordinate

/-- F8: adequacy conjunction on the rank-two pair. -/
example : (OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (0 : Fin 2))
    (OddMath.SkewPolynomial.generator 1)
  + OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (1 : Fin 2))
    (OddMath.SkewPolynomial.generator 0) = 0)
  ∧ (OddMath.SkewPolynomial.mul
    (OddMath.SkewPolynomial.generator (0 : Fin 2))
    (OddMath.SkewPolynomial.generator 0) ≠ 0) :=
  OddMath.PbwL1.adequacy 0 1 (by decide)

end OddMath.PbwL1.Tests
