# Corrected coordinate basis with arbitrary old endpoints

This is the source-coordinate automorphism needed for arbitrary-old-Hom
row division in [DeformedBoundaryDivision](DeformedBoundaryDivision.md), §5.
The implementation is
[ELVOffDiagonalCorrectedCoordinates](../../OddMath/QuiverHecke/CyclotomicAction/ELVOffDiagonalCorrectedCoordinates.lean).

For an odd moving colour, let T be total parity twist on Old(v,t), and
let Δ be the signed old-source delta action from `offDiagonalCoefficientRho`.
The corrected source lift in degree 2q extracts to `single(2q,b)`;
in degree 2q+1 it extracts to

    single(2q+1,T(b)) + single(2q,Δ(b)).

These formulas are derived from the full-coefficient actual rho iterates,
not stipulated as coordinates. The supplied long-section/actual-rho
comparison handles arbitrary old endpoints and the empty old Hom.

The finite triangular change sends each adjacent pair (a,b) to
(a+Δ(b),T(b)). Its inverse is (c,d) to (c-Δ(T(d)),T(d)); only the involutivity
of T is needed for these inverse identities. Finite support is preserved.
`offDiagonalCorrectedCoordinateEquiv_single` identifies each forward
single-column value with extraction of the actual corrected lift.

All old coefficients remain full polynomial/exterior classes over the
supplied commutative ground ring. No ring structure on Old(v,t), field,
nonzero identity, flatness, categorical inverse or action hypothesis is
introduced. This coordinate change is the input to the arbitrary-Hom
polynomial-row division argument.

Verification status and remaining dependencies are maintained in
[STATUS.md](STATUS.md) and [HANDOFF.md](HANDOFF.md).
