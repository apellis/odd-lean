# Whole finite-family content matrix coordinates

Brundan--Ellis (1.13)--(1.14), as used in DeformedMatrixComparison (4), (5),
requires the given shifted unit-source and cap-target families. The
content and old families now have genuine coordinatewise linear
equivalences without any inverse-matrix or chart-evenness premise.

`oldContentUnitSlotEquiv` and `oldContentCapSlotEquiv` remove the canonical
content parity coordinate, apply the selected E/F or inclusion-unit value
chart from `ContentMatrixCharts.md`, and insert the canonical old parity
coordinate. They retain both given module parity actions. The principal
unit slot uses the preceding E/F chart; the principal cap slot uses the
following F/E chart; each finite dotted slot uses the given value chart.

`oldContentUnitFamilyEquiv` and `oldContentCapFamilyEquiv` assemble all
coordinates by `LinearEquiv.piCongrRight`. Their `_apply` theorems identify
every coordinate with the specified slot equivalence. The construction
works for every finite count, including count zero with only the principal
mate slot.

The concrete consumer applies the whole equivalences to both moving
parities and repeated-colour contents of heights two, zero and minus two,
using the corresponding nonnegative unit/cap counts. It also tests the
individual odd-shifted finite slot and both whole coordinate formulas on
mixed representable modules, arbitrary output words and arbitrary vectors.
Every producer-owned declaration, including generated declarations, is
audited.

The categories are the untruncated old content categories, with explicit
predecessor content `i :: ν`. Compatibility of all prescribed entries and
the resulting given finite matrix inverses remain separate. In particular,
these invertible coordinate comparisons do not themselves assert that a
matrix is invertible.
