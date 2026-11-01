# Even polynomial boundary division

The moving-parity-zero case of DeformedBoundaryDivision (5) uses the actual
polynomial boundary on arbitrary Old(v,t) coefficients, in its ordinary
source coordinates. The proved leading map is the scalar unit
appendQPProductUnit times oldTwist(p). It is invertible over the supplied
commutative coefficient ring.

ELVEvenRowDivision applies the shared degree-shift module elimination:

- offDiagonalPolynomialBoundary_even_eq_zero_iff identifies its exact kernel
  by support d+endpointQPDegree<outputSDegree.
- offDiagonalPolynomialBoundary_even_injective and
  offDiagonalPolynomialBoundary_even_surjective give the two height ranges.
- evenBoundaryRowDivisionEquiv gives unique quotient/remainder division, with
  quotient support outputSDegree≤d+endpointQPDegree and remainder support
  n+outputSDegree<endpointQPDegree.
- evenBoundaryRowDivisionEquiv_apply reconstructs with the original boundary
  itself and literal remainder inclusion.

There is no corrected-coordinate change in this parity, no coefficient
algebra structure on Old(v,t), and no field, dimension, flatness or
categorical crossing-inverse assumption.

The producer and mixed-parity concrete consumer pass scoped builds with
warnings as errors. The consumer uses distinct old endpoint orders, checks
both inverse identities and literal reconstruction, instantiates the exact
kernel statement, and proves injection/surjection hypotheses in both
height ranges with positive cutoffs. It audits the seven owned producer
declarations and all thirty shared division declarations. Full CI and the
global audit remain integration gates.

The even balanced crossing height consequences, snake comparison and cap
matrix are subsequent steps. Their categorical cap normalization differs
from the odd shifted-source one: the even source uses coefficient(0).
