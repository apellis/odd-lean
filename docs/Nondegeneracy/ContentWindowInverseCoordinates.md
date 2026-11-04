# Finite content inverse window coordinates

For BE (1.13)–(1.14) and `SwappedHomInversion.md` §4 (7), the finite
`g'` entries are forced by the prescribed forward mate and unit/cap fields.
`ELVContentWindowInverseCoordinates` proves four coordinate equations:

* `contentSupportedLocalInverseFrom_window`: every finite row `g' m`
  of a supported unit-orientation record is the weighted content inverse
  row through the target and value charts.
* `contentSupportedLocalInverseTo_window`: every finite column `g' m`
  of a supported cap-orientation record is the weighted content inverse
  column through the value and source charts.
* `contentTargetsLocalInverseFrom_window`: the first equation with the
  stored successor contents and their specified equality proofs.
* `contentTargetsLocalInverseTo_window`: the second equation with the
  stored successor contents and their specified equality proofs.

All four equations apply to **every** local inverse record with those
forward fields. They assume only that `m` lies in its finite window; no
comparison of inverse maps is an additional hypothesis. The proof uses
joint detection by the forward columns or rows together with the inverse
identities. Fields beyond the window remain unconstrained.

The module and its paired
`scripts/NonVacuity/ELVContentWindowInverseCoordinates.lean` consumer passed
Lean 4.34.1 with warnings as errors, both repository compatibility options,
and default limits. The consumer audits all 77 declarations owned by the
module against `propext`, `Classical.choice`, and `Quot.sound`.
Its concrete fixture has both moving parities, chosen records on content
`[i]` in the unit orientation and `[i,i,i]` in the cap orientation, and
quantifies over every finite window index. Both canonical and explicit
successor-content charts are exercised.

This result supplies the content-record attachment of the finite chosen
`g'`. It does not establish its source coefficient degree. The remaining
boundary attachment must identify each weighted finite inverse row/column
with its raw OLD kernel coordinate, retain the canonical parity shifts,
and compose with the ordinary unit/cap evaluation. The positive raw unit
orientation corresponds to weight-negative `boundaryNeg(r,j)`; the
negative raw cap orientation corresponds to weight-positive
`boundaryPos(j,r)`. Only after those comparisons can the raw difference
degree `2 dᵢ(r-j)` replace the module-Hom grading assumption in the chosen
reservoir boundary ideal membership theorems.
