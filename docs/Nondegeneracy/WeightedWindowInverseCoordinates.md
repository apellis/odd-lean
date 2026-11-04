# Weighted finite inverse window coordinates

For the finite inverse boundary contractions of
`SwappedHomInversion.md` §4 (7),
`ELVWeightedWindowInverseCoordinates` supplies the finite weighted-to-OLD
inverse attachment with its canonical parity charts.

* `weightedContentLocalInverseFrom_window_total` evaluates the chosen
  weighted local `g' j` as the literal inverse matrix row `some j`,
  followed by the named source parity isomorphism.
* `weightedContentLocalInverseTo_window_total` evaluates the chosen
  weighted local `g' j` as the inverse matrix applied to the literal
  target insertion `some j`, after its named inverse parity isomorphism.
* `weightedUnitInverse_window` extracts every finite coordinate of the
  already proved full weighted-to-OLD inverse chart.
* `weightedContentUnitWindow_chart` and
  `weightedContentCapWindow_chart` identify these chosen weighted `g'`
  fields with the OLD inverse row and column, respectively.
* `weightedCapWindowInput_coordinates` retains every finite cap input
  under the full target chart.

No inverse comparison is a premise: the existing forward matrix charts
force the full inverse charts, which force these finite coordinate
equations. Every index is a `Fin` of the prescribed unit/cap count.

The producer and paired
`scripts/NonVacuity/ELVWeightedWindowInverseCoordinates.lean` consumer
passed Lean 4.34.1 with warnings as errors, both repository compatibility
options and default limits. The consumer audits all 26 owned declarations
against the three allowed axioms. Its representable-module fixture has
both moving parities, every finite unit row in windows of sizes 8 and 10,
and every finite cap column in a window of size 1.

Together with `ELVKernelBoundaryEvaluation`, these equations attach the
chosen weighted finite windows to the raw OLD kernel inverse coordinates.
The remaining boundary calculation composes them with the ordinary
unit/cap rows and columns and transports their source coefficient degree
to the chosen reservoir coefficient. Chosen reservoir ideal membership
is not a conclusion of this module.
