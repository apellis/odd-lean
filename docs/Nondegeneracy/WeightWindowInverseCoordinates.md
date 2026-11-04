# Chosen weight finite inverse coordinates

`ELVWeightWindowInverseCoordinates` supplies the supported weight-block
attachment for the finite inverse fields in `SwappedHomInversion.md`
§4 (7). `elvChosenCapWindow` and `elvChosenUnitWindow` are the literal
`g'` fields chosen by `elvRouquierFamily.loc`, evaluated on a whole-weight
input and its selected output block.

`elvCapWindow_coordinates` and `elvUnitWindow_coordinates` prove that
every finite row or column of any inverse of the prescribed weight
matrix has the constructed content inverse coordinate. Their specialized
`elvChosenCapWindow_coordinates` and `elvChosenUnitWindow_coordinates`
apply to the literal chosen fields. The finite index condition is exactly
membership in the positive or negative weight window. The comparison is
forced by the forward matrix and its inverse identities, not supplied
as an additional hypothesis.

The producer and paired
`scripts/NonVacuity/ELVWeightWindowInverseCoordinates.lean` consumer passed
Lean 4.34.1 with warnings as errors, both repository compatibility options
and default limits. The consumer audits all 32 owned declarations against
the three allowed axioms. Its fixture has both moving parities, both
strict height orientations, every finite index and separately checked
nonempty windows.

These coordinates concern blocks with a predecessor. Absent lower
induction kills cap boundaries but does not generally kill unit-window
boundaries. The unit fields on those absent blocks require the separate
zero-principal content inverse comparison. No reservoir boundary degree
or coefficient-ideal membership is concluded here.
