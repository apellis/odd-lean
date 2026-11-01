# Module-valued degree-shift division

The polynomial elimination in DeformedBoundaryDivision (5) depends on
module addition, scalar multiplication and invertible leading coefficient
maps, rather than multiplication of old Hom coefficients.

OddMath.Algebra.DegreeShiftRow takes a row A on finitely supported
module-valued coefficients, natural degrees S,Q, and specified leading
equivalences L(n). Its single-column above/top hypotheses state that a
column d vanishes at n when d+Q<n+S, and its pivot at n+S=d+Q is L(n).

The declarations eq_zero_iff, division, separation and divisionEquiv give
the exact low kernel and unique high-quotient/low-remainder decomposition.
The allowed quotient support satisfies S≤d+Q; the remainder support
satisfies n+S<Q. The declarations injective and surjective specialize
the nonnegative and nonpositive degree ranges.

The existing odd arbitrary-Hom API in ELVOffDiagonalRowDivision is
preserved as corollaries of this theorem, using the proved corrected
coordinate row and its actual leading maps. Its downstream splitting
consumer still checks. The even specialization uses ordinary source
coordinates and the actual even leading maps; it is a separate consumer
of this same elimination theorem.

Scoped verification passes with warnings as errors. The independent
integer shift-by-two consumer checks both inverse identities and an
explicit nonzero pivot, and audits all owned declarations. These are
scoped checks; full CI and the global audit remain integration gates.
