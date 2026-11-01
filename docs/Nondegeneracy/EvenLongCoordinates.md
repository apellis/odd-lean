# Even moving-dot long coordinates

This is the parity-zero specialization of
[DeformedMackeyBoundary](DeformedMackeyBoundary.md), equations (2)-(3).

For an even moving colour i, the source first dot is the literal moving dot,
and its coefficient operator is the ordinary finite shift
`evenLongShift`. The full old class in Old(v,t) stays unchanged, including
its exterior coefficients. No delta correction or total-coefficient twist
is present because parity(i) is zero.

The proposed producer `ELVEvenLongCoordinates` proves the moving-dot recurrence
on every arbitrary-endpoint source class and on the prescribed long section.
The empty old Hom is handled explicitly. Its concrete consumer uses connected
mixed-parity Cartan data, reversed old words, and an odd exterior coefficient.

## Independent S comparison still required

The existing generic theorem `outputLongExtraction_move_independentS`
identifies the base moving intertwiner with independently defined S.
The existing `pMap_evenDot_move_iterate` gives its ordered reverse-QP image.
The next comparison must combine those identities with the even extraction
recurrence and actual C0P factorization. Unlike the odd case, ordinary shift
acts correctly at every degree, so S need not have only even support.

The generic numerator leading and monic-S right-division arguments can then
supply the even polynomial-boundary degree and top coefficient.
This producer does not assert that comparison or an even categorical inverse.
Source and concrete consumers await CI.
