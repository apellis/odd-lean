# Off-diagonal long coordinates

This is the arbitrary-old-Hom coordinate input to
[DeformedMackeyBoundary](DeformedMackeyBoundary.md), equation (2).
The implementation is
[ELVOffDiagonalLongCoordinates](../../OddMath/QuiverHecke/CyclotomicAction/ELVOffDiagonalLongCoordinates.lean).
It retains full polynomial/exterior old coefficients over an arbitrary
commutative ground ring, both moving parities, arbitrary old words v,t,
and arbitrary balance parity p.

## Construction

For an existing old normal-form index y from v to t, rebase the canonical
long moving tail on t using y. Its old target is t, and its moving exponent
is unchanged. The prescribed old-quotient coordinate and the paired long
tail give maps `longHomCoordinate` and `longHomLift`, normalized by the
source-word sign `zsign(p(i)*wordSumParity(v))^m`.

Same-tail extraction reads back every full old coefficient; different moving
exponents have zero readback. Affine PBW finite support therefore assembles
`longHomExtraction` into an actual finite polynomial row over Old(v,t).
The finite sum of the paired tails is `longHomSection`, and their composite
is the identity. This uses neither flatness nor a detecting action.

Rebasing changes only the old normal form, not the moving tail. Both the lift
and coordinate functional are proved independent of y. If no old normal-form
index exists, the affine old Hom and its actual quotient vanish. Thus
`offDiagonalLongExtraction` and `offDiagonalLongSection` require no supplied
old index, include empty old Homs, and satisfy extraction after section =
identity. In particular extraction is surjective and section is injective.

## Claim boundary and next comparison

The source has compiled with warnings as errors; the importing concrete
consumers and full package/axiom gates remain required before integration.
The consumer uses connected all-odd data with reversed old words and also
different strand counts, so both off-diagonal and empty-Hom cases occur.

These coordinate maps alone do not identify their entire kernel with the
chronological short span. That exact kernel, output-old transport,
off-diagonal polynomial boundary and leading-map comparison, naturality,
and the full categorical inverse remain subsequent obligations. A diagonal
matrix equivalence is not silently promoted to an off-diagonal bimodule
equivalence.

## Proposed exact short kernel

The companion module `ELVOffDiagonalLongKernel` extends the chronological
kernel calculation to arbitrary v,t. Long shuffles ending at t++[i] have
old target t; every other moving tail belongs to the chronological short
span. Existing arbitrary-endpoint chronological normalization kills each
short generator under the full coefficient extraction. Reconstruction then
gives exactly

    ker(offDiagonalLongExtraction p i v t) = chronologicalShortSpan i v t.

If the old normal-form index type is empty, every occurring tail must be
short, since a long one would itself supply an old normal-form index.
Consequently no inhabitation assumption is needed. This exact-kernel
extension is proposed until its source, consumer and full CI gates pass.
The off-diagonal polynomial boundary and leading-map transport remain next.
