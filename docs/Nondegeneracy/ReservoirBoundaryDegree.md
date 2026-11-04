# Source degree of the chosen reservoir boundaries

`ELVReservoirBoundaryDegree` proves the source-coefficient degree required
for the boundary contractions of `SwappedHomInversion.md` §4 (7).
It uses the literal finite `g'` fields selected by
`elvRouquierFamily.loc`, rather than independently supplied inverse maps.

In namespace `ReservoirBoundaries`, the final APIs are:

* `positiveCoefficient_mem_degree`: the reconstructed coefficient of
  literal `boundaryPos(j,r)` lies in source degree `2 dᵢ(r-j)`, provided
  `j < (D.h i x₁).toNat`.
* `negativeCoefficient_mem_degree`: the reconstructed coefficient of
  literal `boundaryNeg(r,j)` lies in the same source degree, provided
  `j < (-D.h i x₁).toNat`.

Both retain arbitrary output content blocks, arbitrary ordinary dot
powers `r`, the standing cutoff/highest-weight match, a symmetrizer and
homogeneous admissible parameters. They add no inverse-degree,
module-Hom grading, inverse-comparison or whole-weight nilpotence premise.
The finite-window hypothesis is exactly the source's restriction on the
chosen `g'` field. Strict positivity follows when `j < r`.

The supported weight finite inverse coordinates first identify the
chosen `g'` with a constructed content inverse. The prescribed unit/cap
squares and the finite content inverse uniqueness equations then identify
the literal boundary with the given weighted local boundary. Its source
coefficient action and difference degree are supplied by the checked
arbitrary-content weighted boundary calculation.

The two orientations handle absent predecessors differently. A finite
positive-height cap slot forces strictly positive weight height; the
existing predecessor theorem therefore supplies a supported block for
every output. The negative-height unit window survives without a
predecessor. `negative_absent_content_coordinates` and
`negative_absent_weighted_coordinates` retain its constructed absent
content inverse, and `negative_weighted_coordinates_all` combines the
supported and absent cases. No absent unit boundary is set to zero.

`positiveRepresentedValue` and `negativeRepresentedValue` are the raw
source endomorphisms with their exact stored finite counts.
Their `_degree` theorems retain the inherited truncated source grading.
`positive_represented_coordinates` and
`negative_represented_coordinates` identify the literal chosen boundary
action on each module vector. The content action theorems extend this to
every exact-content module by the named module-action predicate and
generic family-extension argument. Evaluating on representable modules
then proves the two reconstructed coefficient degree statements above.

The producer and paired
`scripts/NonVacuity/ELVReservoirBoundaryDegree.lean` consumer passed Lean
4.34.1 with warnings as errors, both repository compatibility options
and default limits. The consumer audits all 144 owned declarations
against the three allowed axioms. It exercises both moving parities,
both strict height orientations, unequal symmetrizers, every finite
window slot, and ordinary rows beyond the finite window. Its absent
rank-one odd fixture has a separately detected nonzero vacuum vector;
literal `boundaryNeg(0,0)` acts nonzero as identity on that vector, while
the all-output negative source-degree theorem also covers every finite
slot with rows beyond the window.

The realization equations in `ELVReservoirBoundaries` identify these
reconstructed coefficients with the literal chosen reservoir boundaries
on every whole-weight input. Combining those equations, source degree
positivity and the source coefficient ideal transport supplies the
remaining boundary membership in `J₁`. That ideal transport is separate
from the source-degree result proved here.
