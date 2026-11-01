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

## Arbitrary-Hom polynomial-row division and splitting

The draft `ELVOffDiagonalRowDivision` composes the actual polynomial boundary
with the corrected-coordinate equivalence and eliminates its highest
nonzero coefficient using `offDiagonalBoundaryLeadingEquiv`. This is finite
module-valued division on Old(v,t); it uses no multiplication on this Hom.

The draft `ELVOffDiagonalRowSplitting` proves unique high-source/low-output
normal forms, the literal positive-window assembly, the corrected low-kernel
equivalence, a right inverse in nonpositive height, and the positive row
cokernel. Both old endpoints are arbitrary. Height degrees depend on the
source word v, as in the concrete boundary formulas. Moving colour is odd.

The concrete consumer uses connected mixed B2 data with source and target
orders reversed. It also instantiates the negative branch with repeated odd
colour. Both inverse products and the owners' axiom audit are included.
These additions await CI together with their proposed leading-coordinate
dependencies. They do not assert the balanced crossing inverse or the
categorically normalized cap matrix; the arbitrary-Hom snake and cap
comparison remain subsequent prerequisites.
