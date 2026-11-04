# Residual inversion for a negative probe height

`CentralInverse/ResidualComparisonNegative` supplies the negative probe-height
subcases (b), (c) of ProbeWindowInverse §3 in the coefficient-ideal comparison
of SwappedHomInversion (11)–(12). The existing MixedCases theorems already
prove the auxiliary window inverses; these new statements attach the residual
matrix and its coefficient-ideal error.

`isIso_posMap_of_cap_of_cup_window` uses a reservoir cap window of length
H+b, a probe unit window of length b, and H fused cap rows.
`isIso_negMap_of_cup_of_cup_window` uses a reservoir unit window of length
k, a probe unit window of length b, and k+b fused unit columns.
Thus neither statement requires a nonnegative probe height.

The separated mixed-bend equality, exact reservoir inverse and positive
closure/off-window memberships remain intermediate construction inputs.
Finite-window contractions follow from the given inverse. Outside the
window their differences lie in the first coefficient-ideal level.
Lifting from the appropriate auxiliary map then proves the specified
two-sector map invertible. `caseBNegMap` retains both off-corner signs;
its reference inverse is obtained by the explicit sign diagonal.

The producer and concrete consumer pass strict checking, including all
five owned standard-axiom audits. The consumer uses rational module categories with a negative probe height of minus one.
The positive fused case retains a nonzero mixed bend; the negative fused
case retains two nonzero unit columns and a triangular augmented matrix.
No inverse of the residual matrix is assumed. Full integration remains
separate from these scoped checks.
