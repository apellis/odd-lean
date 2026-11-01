# Corrected rho with arbitrary old endpoints

This is the arbitrary-old-Hom source-operator comparison for
[DeformedMackeyBoundary](DeformedMackeyBoundary.md), equations (2)-(3).
The implementation is `ELVOffDiagonalRho`, full-CI verified in #785.

For an odd moving colour j and old source v, target t, the finite row
operator `offDiagonalCoefficientRho` is

    shift ∘ oldTwist(p(j),v,t)
      + zsign(p(j)*wordSumParity(v)) · 2(-1)^cutoff(j)
          · oldPrecomp(twist(p)(delta_v)).

The delta term acts at v; the total parity twist acts on the entire
coefficient in Old(v,t). Neither is discarded or replaced by a scalar
centrality assertion.

The actual `boundaryRho` on Target(j,v,t++[j]) acts on every normalized
long lift by these two prescribed terms. Finite assembly gives
`boundaryRho_offDiagonalLongSection`, including empty old Homs with no
supplied old index. Define `offDiagonalCorrectedLift` by actual source-rho
iteration of the degree-zero long section. The section intertwines every
iterate, and extraction of that actual corrected lift is exactly the
corresponding coefficient-rho iterate.

All coefficients are full polynomial/exterior old Homs over the supplied
commutative ground ring and scalar data. The source and concrete consumer passed full build, global axiom audit and
non-vacuity checks before research integration in #785.
It supplies no coefficient/output covariance, leading law, categorical
counit/cap identification, matrix inverse, or full factor action; those
remain distinct comparisons in the overall proof.
