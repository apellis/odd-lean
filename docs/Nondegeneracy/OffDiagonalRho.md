# Corrected rho with arbitrary old endpoints

This is the arbitrary-old-Hom source-operator comparison for
[DeformedMackeyBoundary](DeformedMackeyBoundary.md), equations (2)-(3).
The implementation is
[ELVOffDiagonalRho](../../OddMath/QuiverHecke/CyclotomicAction/ELVOffDiagonalRho.lean).

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
commutative ground ring and scalar data.

## Extraction recurrence on every old-only class

[ELVOffDiagonalRhoExtraction](../../OddMath/QuiverHecke/CyclotomicAction/ELVOffDiagonalRhoExtraction.lean)
extends the comparison from the selected
section to every z in Target(j,v,t++[j]). Generic PBW coordinate identities
give normalized moving-power transport, the old-source action, zero-degree
vanishing for positive moving powers, and the literal zero/successor
corrected-rho coefficient recurrence. Finite assembly and the empty-index
case give

    offDiagonalLongExtraction (boundaryRho z)
      = offDiagonalCoefficientRho (offDiagonalLongExtraction z).

Thus the actual extraction kernel is rho-stable. The exact chronological
kernel identifies this with short-span stability, so rho iterates preserve
an initial modulo-short comparison.

Verification status and remaining dependencies are maintained in
[STATUS.md](STATUS.md) and [HANDOFF.md](HANDOFF.md).
