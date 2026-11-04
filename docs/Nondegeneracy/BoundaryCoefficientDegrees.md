# Finite inverse boundary coefficients

The boundary contractions in `SwappedHomInversion.md` §4, equation (7),
require degrees of the chosen finite `g'` entries, independently of the
principal inverse used in equation (8). The source coefficient calculation
uses the intrinsic shifted OLD kernel coordinates, rather than a grading
on arbitrary module Homs.

`ELVKernelBoundaryDegrees` defines the literal positive inverse row
`positiveKernelWindowInverse` at every finite unit coordinate, and the
literal negative inverse column `negativeKernelWindowInverse` at every
finite cap coordinate. Both have raw degree `-2 dᵢ j`. Applying the positive
inverse row `j` after unit/dot column `r` gives `positiveKernelBoundary` of
degree `2 dᵢ(r-j)`. Applying cap/dot row `r` after negative inverse column
`j` gives `negativeKernelBoundary` of the same degree. These statements
hold for every finite `j` and every natural `r`;
`kernelBoundaryDegree_pos` proves strict positivity when `j < r`.

The names positive and negative here refer to **content crossing height**.
That height is opposite to weight height: the positive raw unit
orientation corresponds to `boundaryNeg(r,j)`, and the negative raw cap
orientation corresponds to `boundaryPos(j,r)` on the reservoir.

The finite chosen inverse is attached in three steps. First,
`ELVKernelBoundaryEvaluation` identifies all OLD inverse rows and columns
with their raw coefficient action, retaining the canonical parity shifts.
Second, `ELVWeightedWindowInverseCoordinates` identifies all finite `g'`
fields of the constructed weighted local inverse with those OLD rows and
columns. Third, `ELVContentWindowInverseCoordinates` forces every finite
`g'` of any local record with the prescribed forward fields to equal that
weighted local inverse through the content source, target and value
charts. The finite-index restriction is essential: an arbitrary local
record does not constrain `g'` beyond its prescribed window.

`ELVWeightedKernelBoundaryCoordinates` composes the first two steps with
the ordinary unit/cap evaluation. Its two literal chosen weighted
contractions are `weightedContentUnitBoundaryValue` and
`weightedContentCapBoundaryValue`. Their `_atWord` equations identify the
values at every OLD word with the raw boundary action. Their `_coefficient`
equations identify the same values with action of the represented source
endomorphisms `weightedUnitBoundaryCoefficient` and
`weightedCapBoundaryCoefficient`. Finally,
`weightedUnitBoundaryCoefficient_degree` and
`weightedCapBoundaryCoefficient_degree` prove that both source coefficients
lie in the inherited truncated degree `2 dᵢ(r-j)`. There is no added
inverse-degree premise and no grading of arbitrary module Homs.

The weighted boundary producer and its paired
`scripts/NonVacuity/ELVWeightedKernelBoundaryCoordinates.lean` consumer
passed Lean 4.34.1 with warnings as errors, both repository compatibility
options and default limits. The consumer audits all 25 owned declarations
against the three allowed axioms. It tests representable modules, both
moving parities, every finite window slot in both height orientations,
unequal symmetrizer values, arbitrary ordinary dot powers, the chosen
weighted contraction evaluations, and the represented source degrees.
The preceding coordinate and raw-degree modules have their own checked
consumers and separate mathematical notes.

The remaining reservoir attachment is the comparison of the **chosen
weight/reservoir finite `g'`**, followed by arbitrary stored-content and
absent-block transport. The weight analogue of the checked principal
inverse comparison must retain every finite `g'` coordinate; the
principal equations alone do not imply it. On supported blocks this must
be composed with `contentTargetsLocalInverseFrom_window` or
`contentTargetsLocalInverseTo_window`, the weighted boundary equations,
and the source coefficient action criterion. Arbitrary content requires
transport of the finite index and its count together with the object.
Absent blocks require their separate content support calculation.

Thus the weighted local boundary source degree is checked, while chosen
reservoir boundary degree and coefficient-ideal membership remain to be
attached. No nilpotence of an entire weight category is introduced or
claimed. Raw difference degree alone is not used as a proof of chosen
reservoir ideal membership.
