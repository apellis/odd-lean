# Even moving-dot long coordinates

This is the parity-zero specialization of
[DeformedMackeyBoundary](DeformedMackeyBoundary.md), equations (2)-(3).

For an even moving colour i, the source first dot is the literal moving dot,
and its coefficient operator is the ordinary finite shift
`evenLongShift`. The full old class in Old(v,t) stays unchanged, including
its exterior coefficients. No delta correction or total-coefficient twist
is present because parity(i) is zero.

The implementation
[ELVEvenLongCoordinates](../../OddMath/QuiverHecke/CyclotomicAction/ELVEvenLongCoordinates.lean)
proves the moving-dot recurrence
on every arbitrary-endpoint source class and on the prescribed long section.
The empty old Hom is handled explicitly. Its concrete consumer uses connected
mixed-parity Cartan data, reversed old words, and an odd exterior coefficient.

## Independent S comparison

The generic theorem `outputLongExtraction_move_independentS` identifies the
base moving intertwiner with independently defined S. The theorem
`pMap_evenDot_move_iterate` gives its ordered reverse-QP image.
[EvenPolynomialBoundary](EvenPolynomialBoundary.md) combines these with the
even extraction recurrence and C0P factorization. Ordinary shift acts at
every degree, so S need not have only even support.

The source section retains its supplied balance parity p.
[EvenOffDiagonalLeading](EvenOffDiagonalLeading.md) records the resulting
balance twist on the old coefficient in the boundary leading map.

Verification status and remaining dependencies are maintained in
[STATUS.md](STATUS.md) and [HANDOFF.md](HANDOFF.md).
