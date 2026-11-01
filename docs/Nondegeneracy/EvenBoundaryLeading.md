# Leading coefficients of the even polynomial boundary

This is the parity-zero independent-S argument in
[DeformedBoundaryDivision](DeformedBoundaryDivision.md), section 5.

Let Φ_d be the actual generic polynomial boundary applied to
single(d, old identity). The canonical diagonal extraction compatibility
transfers the established full old-arrow covariance to this same boundary.
Since every independent-S coefficient is twist invariant, its coefficient
postcomposition commutes with the boundary.

The high-coordinate recurrence and this covariance identify, above degree(S),
the coefficients of S times Φ_d with the ordered reverse numerator.
The independently proved numerator bound and unit top, together with monic-S
bound detection, give

    Φ_d(m) = 0 if d+endpointQPDegree < m+degree(S),

and, when degree(S) ≤ d+endpointQPDegree,

    Φ_d(d+endpointQPDegree-degree(S))
      = appendQPProductUnit · old identity.

If d+endpointQPDegree < degree(S), the entire actual row is zero.
These are prescribed support bounds and top values, including zero old
corners; they do not assert a nonzero degree.

The implementation is
[ELVEvenBoundaryLeading](../../OddMath/QuiverHecke/CyclotomicAction/ELVEvenBoundaryLeading.lean).
The result concerns the diagonal identity row.
[EvenOffDiagonalLeading](EvenOffDiagonalLeading.md) transports it to arbitrary
old Homs, retaining balance twist oldTwist(p).

Verification status and remaining dependencies are maintained in
[STATUS.md](STATUS.md) and [HANDOFF.md](HANDOFF.md).
