# Finite unit windows at absent predecessor blocks

`ELVAbsentWindowInverseCoordinates` attaches the finite chosen unit
inverse rows of `SwappedHomInversion.md` §4 (7) on blocks without a lower
predecessor. These rows must be retained: the principal closure vanishes
through lower induction, whereas the unit boundary need not vanish.

`contentAbsentUnitInverse_window` compares every finite row of a
zero-principal content inverse with the chosen weighted content inverse
through its target and value charts.
`contentAbsentUnitTargetInverse_window` retains an arbitrary stored upper
successor content. Forward unit columns jointly detect maps, so the
comparison is derived from the two inverse identities rather than given
as an additional hypothesis.

`elvContentAbsentUnitInverseAtWeight` is the constructed absent content
record at the actual upper successor. The ordinary upper-loop unit chart
is `elvWeightUnitPower_following_coordinates`.
`elvAbsentUnitWindow_coordinates` forces every finite weight inverse row
to have that content coordinate, and
`elvChosenAbsentUnitWindow_coordinates` specializes it to the literal
`g'` selected by `elvRouquierFamily.loc`.

The producer and paired
`scripts/NonVacuity/ELVAbsentWindowInverseCoordinates.lean` consumer passed
Lean 4.34.1 with warnings as errors, both repository compatibility options
and default limits. The consumer audits all 54 owned declarations against
the three allowed axioms. It exercises both finite slots of a rank-one
odd unit window at an absent predecessor, with the stored upper content.
It separately detects a nonzero vacuum vector via the nonzero one-strand
odd quotient, and proves that literal `boundaryNeg(0,0)` acts as identity
on that vector. Thus this absent branch cannot be replaced by zero.

These are coordinate equalities. The reconstructed reservoir boundary
source degree requires composing them with the arbitrary-content
weighted boundary coefficient action and its inherited integer grading.
No module-Hom grading or whole-weight nilpotence hypothesis is used.
