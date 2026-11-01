# Polynomial-row and input-matrix inverses on arbitrary old Homs

This implements finite division in [DeformedBoundaryDivision](DeformedBoundaryDivision.md),
section 5, and the inversion argument in
[DeformedRouquierMatrix](DeformedRouquierMatrix.md), section 4, with independent old
source and target words. The moving colour j is odd. The supplied commutative
ground ring, scalar datum and full polynomial/exterior coefficients are retained.

Write H=Old(v,t), M=endpointQPDegree(j,v) and S=outputSDegree(j,v). No ring
structure on H is used. The actual finite long extraction has kernel equal
to the prescribed alpha range; correcting its section by the alpha coordinate
gives `offDiagonalSourceCoordinateEquiv`. This source splitting itself works
at every moving colour.

## Concrete polynomial-row normal forms

The actual polynomial boundary A acts on finitely supported H-valued rows.
The corrected-coordinate equivalence comes from extraction of actual rho
iterates. The coefficient above each corrected pivot vanishes, and the pivot
is the explicit unit-times-whole-coefficient-twist map
`offDiagonalBoundaryLeadingEquiv`.

`offDiagonalBoundaryRowDivisionEquiv` gives unique high-source/low-output
division. The high source consists of d with S≤d+M; the output window consists
of n with n+S<M. `offDiagonalBoundaryKernelEquiv` identifies the boundary
kernel with corrected source coordinates d+M<S. Positive and negative row
splittings, a nonpositive-height section, and the positive row cokernel are
constructed from these concrete maps.

## The prescribed crossing and its kernel

The short crossing decoder is the inverse on the genuine crossing span.
The original P map, corrected long section, decoder and q construct
`offDiagonalBoundarySnake`. Its range is exactly the kernel of the prescribed
cyclotomic crossing; `offDiagonalBoundarySnakeKernelEquiv` packages both
directions. The snake class depends only on long extraction, permitting the
uncorrected rho-compatible lift in subsequent cap computations.

`offDiagonalPositiveCrossingEquiv` identifies the enlarged old Hom with
Source(j,v,t) and the literal low output-polynomial window when S≤M.
Its forward map is the prescribed crossing plus the canonical append
projection of the literal output embedding.

## Input contraction and moving dot

`ELVOffDiagonalInputOperators` defines the affine contraction as the constant
coefficient of appendC0InputDefect after shortCross. The affine dot is the
moving append operator transported by shortCross and its decoder. Corrected
rho preserves the alpha range, so these two specified maps preserve the
Pprime relations and descend to the independently defined Source.

The descended maps satisfy
`offDiagonalInputContraction_q` and `offDiagonalCrossingInputDot_q`.
Their representative formulas keep parity on the entire old coefficient.
No chosen cap row, kernel exactness or comparison map is a hypothesis.

For y(f)=decode(P(longSection(f))), the affine dot sends y(f) to y(rho f),
and contraction gives A(rho f)(0). Thus on the actual corrected degree-d lift,
the r-th contraction vanishes if r+d+1+M<S, and equals exactly
`offDiagonalBoundaryLeadingEquiv ... 0` when S=r+d+1+M.
These are `offDiagonalInputContractionAffine_corrected_below` and
`offDiagonalInputContractionAffine_corrected_pivot`.

## Negative-height input matrix

At S=M+m, `offDiagonalInputMatrixEquiv` is the k-linear equivalence

    Source(j,v,t) ≃ Old(v++[j],t++[j]) × (Fin m → H).

Its forward map is the actual cyclotomic crossing together with the specified
rows E, EX, ..., EX^(m−1). On the actual crossing kernel, the low corrected
columns give an anti-triangular matrix with the concrete invertible pivot
above. Reversing columns and applying the existing finite triangular
nilpotence lemma proves bijectivity of that restriction. Crossing surjectivity
then reconstructs the entire matrix.

The argument works over the supplied commutative ground ring, including m=0.
It uses neither finite-dimensionality nor a field, flatness, a faithful action,
a ring on H, or a diagonal-endpoint sufficiency claim.

## Scope and verification

The production modules and their concrete consumers have passed scoped
warnings-as-errors checks with the pinned transparency settings. The input
consumer audits every declaration owned by InputOperators, InputPivots,
InputMatrix and the finite triangular lemma. The source/row/snake/positive
consumers audit their respective production owners.

The input consumer uses connected mixed B2 data over Q, with the odd moving
colour. At negative height three it takes source [even,odd,odd,odd], target
[odd,even,odd,odd], and cutoffs 1 on odd and 3 on even. It checks both inverse
products, the actual third-row pivot, a below-pivot zero, and both q-descent
identities. The zero-row case uses positive cutoffs 2 on odd and 3 on even,
source [even,odd,odd] and target [odd,even,odd]. Both inverse products are
checked there as well.

Full CI and the global axiom audit remain integration gates. These are
k-linear input-oriented inverses on arbitrary old endpoints. Identification
with the prescribed categorical counit/dotted rows, canonical source parity
transport, and naturality remain separate explicit obligations.
