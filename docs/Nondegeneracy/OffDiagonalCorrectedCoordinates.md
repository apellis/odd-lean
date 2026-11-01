# Corrected coordinate basis with arbitrary old endpoints

This is the source-coordinate automorphism needed for arbitrary-old-Hom
row division in [DeformedBoundaryDivision](DeformedBoundaryDivision.md), §5.
The proposed implementation is `ELVOffDiagonalCorrectedCoordinates`.

Let T be total parity twist on Old(v,t), and let D be the signed old-source
delta action from `offDiagonalCoefficientRho`. The actual even corrected
source lift extracts to `single(2q,b)`; the actual odd lift extracts to

    single(2q+1,T(b)) + single(2q,D(b)).

These formulas are derived from the full-coefficient actual rho iterates,
not stipulated as coordinates. The supplied long-section/actual-rho
comparison handles arbitrary old endpoints and the empty old Hom.

The finite triangular change sends each adjacent pair (a,b) to
(a+D(b),T(b)). Its inverse is (c,d) to (c-D(T(d)),T(d)); only the involutivity
of T is needed for these inverse identities. Finite support is preserved.
`offDiagonalCorrectedCoordinateEquiv_single` identifies each forward
single-column value with extraction of the actual corrected lift.

All old coefficients remain full polynomial/exterior classes over the
supplied commutative ground ring. No ring structure on Old(v,t), field,
nonzero identity, flatness, categorical inverse or action hypothesis is
introduced. Source and concrete reversed-word/empty-Hom consumers await CI.
This supplies the coordinate-basis input; actual polynomial-row leading,
division and categorical cap comparison remain separate.
