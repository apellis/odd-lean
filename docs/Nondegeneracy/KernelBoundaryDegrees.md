# Raw finite inverse boundary degrees

The source calculation required by `SwappedHomInversion.md` §4 (7) is
checked in `ELVKernelBoundaryDegrees`. Starting from the literal finite
kernel maps and their already proved bijectivity, it defines
`positiveKernelWindowInverse` at every finite unit row and
`negativeKernelWindowInverse` at every finite cap column. Both have raw
integer degree `-2 dᵢ j`, by their respective `_degree` theorems.

`positiveKernelBoundary_degree` proves that finite inverse row `j` after
ordinary unit/dot column `r` has degree `2 dᵢ(r-j)`.
`negativeKernelBoundary_degree` proves the same degree for ordinary
dot/cap row `r` after finite inverse column `j`.
Both retain arbitrary homogeneous source coefficients, every finite `j`,
and every natural `r`. `kernelBoundaryDegree_pos` proves strict positivity
when `j < r`. No grading on arbitrary module Homs or additional
inverse-degree hypothesis is used.

Here the orientation is named by content crossing height, which is
opposite to weight height. The positive raw unit contraction corresponds
to the weight-negative `boundaryNeg(r,j)`; the negative raw cap
contraction corresponds to weight-positive `boundaryPos(j,r)`.

The module and its paired
`scripts/NonVacuity/ELVKernelBoundaryDegrees.lean` consumer passed Lean
4.34.1 with warnings as errors, both repository compatibility options,
and default limits. The consumer audits all 17 owned declarations against
the repository's three allowed axioms. It uses both odd vertices of the
asymmetric Cartan datum, both unequal symmetrizer values, both height
orientations, every finite coordinate, and rows/columns strictly beyond
the whole finite window. Both finite windows are proved nonempty.

`ELVKernelBoundaryEvaluation` and its paired consumer also passed the
same strict checks, auditing all six owned declarations. The APIs
`moduleUnitMatrixIso_window_inv_tensor` and
`moduleCapMatrixIso_window_inv_tensor` identify every finite OLD inverse
row/column with its raw kernel coefficient on a pure tensor, retaining
the canonical parity shifts. `positiveKernelBoundary_evaluate` and
`negativeKernelBoundary_evaluate` then identify the literal OLD module
boundary contractions with the source coefficient action. The consumer
uses representable OLD modules in both orientations and quantifies over
every finite coordinate at both odd vertices.

This raw degree result alone does not prove the chosen reservoir boundary
degree or coefficient-ideal membership. The inverse finite slots must
still be attached to the chosen weighted content and reservoir
`g'` coordinates with their canonical parity charts. The separately
checked `ContentWindowInverseCoordinates.md` supplies the content-record
comparison with the weighted content inverse, rather than the remaining
comparison with the raw OLD kernel slots.
