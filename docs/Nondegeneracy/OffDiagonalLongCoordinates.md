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

## Companion comparisons

Concrete consumers use connected all-odd data with reversed old words and
different strand counts. The exact kernel and polynomial-boundary arguments
below operate on arbitrary old Homs. Output-old transport and the odd/even
leading comparisons are developed in the companion source modules; none
requires promotion of a diagonal-corner equivalence to a bimodule equivalence.

## Exact short kernel

The companion module `ELVOffDiagonalLongKernel` extends the chronological
kernel calculation to arbitrary v,t. Long shuffles ending at t++[i] have
old target t; every other moving tail belongs to the chronological short
span. Existing arbitrary-endpoint chronological normalization kills each
short generator under the full coefficient extraction. Reconstruction then
gives exactly

    ker(offDiagonalLongExtraction p i v t) = chronologicalShortSpan i v t.

If the old normal-form index type is empty, every occurring tail must be
short, since a long one would itself supply an old normal-form index.
Consequently no inhabitation assumption is needed.

## Arbitrary-old-Hom polynomial boundary

`ELVOffDiagonalBoundary` evaluates the actual C₀P on the prescribed
off-diagonal long section to define `offDiagonalPolynomialBoundary`.
Subtracting section after extraction lands in the exact chronological
short kernel; P sends that kernel into the actual crossing span, which C₀
kills. Therefore the literal map factors as

    C₀ P = offDiagonalPolynomialBoundary ∘ offDiagonalLongExtraction.

The construction retains arbitrary old endpoints and both moving parities.
Its factorization uses the prescribed section and exact short kernel.
Odd and even leading transport are developed in
[ELVOffDiagonalBoundaryLeading](../../OddMath/QuiverHecke/CyclotomicAction/ELVOffDiagonalBoundaryLeading.lean)
and [EvenOffDiagonalLeading](EvenOffDiagonalLeading.md), respectively.

Verification status and remaining dependencies are maintained in
[STATUS.md](STATUS.md) and [HANDOFF.md](HANDOFF.md).
