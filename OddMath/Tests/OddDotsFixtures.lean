import OddMath.Diagrammatics.OddDots
import OddMath.DividedDifferences

/-! Hand-derived rank-two odd-dot bridge fixtures; see the development notes for
derivations before implementation. -/
namespace OddMath.Diagrammatics.OddDots.Tests

open OddMath.SkewPolynomial

-- F1: the two dot orders evaluate to opposite monomials.
example : denoteValue [0, 1] = monomial ![1, 1] (-1) :=
  denoteValue_pair_neg

example : denoteValue [1, 0] = monomial ![1, 1] 1 :=
  denoteValue_pair_pos

-- F2: signed exchange is sound on the linear envelope.
example : denoteValue [0, 1] + denoteValue [1, 0] = 0 :=
  signed_exchange_value

-- F3: the unsigned difference is a nonzero doubled monomial.
example : (denoteValue [0, 1] - denoteValue [1, 0]) ![1, 1] = -2 :=
  unsigned_difference_coordinate

-- F4: same-strand dots do not vanish.
example : denoteValue [0, 0] = monomial ![2, 0] 1 :=
  denoteValue_same_zero

-- F5: the length-three stack.
example : denoteValue [0, 1, 0] = monomial ![2, 1] (-1) :=
  denoteValue_triple

-- F6: cross-pack anchors — the bridge monomial coordinates are the same
-- objects the divided-difference pack acts on.
example : OddMath.DividedDifferences.divMonomial 1 1 = 0 :=
  OddMath.DividedDifferences.divMonomial_one_one

example : OddMath.DividedDifferences.divMonomial 2 1 = monomial ![1, 1] 1 :=
  OddMath.DividedDifferences.divMonomial_two_one

end OddMath.Diagrammatics.OddDots.Tests
