# Vacuum layer charts are equality transports

Module: `OddMath/QuiverHecke/SwappedAssembly/SupportedTensorLayerChartTransport.lean`.

Scope: the regular-probe compatibility of the global and local contextual layer
charts used by `VacuumChartCoherence.evaluation` (`VacuumRouteNondegeneracy.lean`),
for the literal dot and both crossing layers of the chosen supported action.

## Checked declarations

In the strict 2-supercategory `Π-𝔖ℭ𝔞𝔱`, every chart below is a composite of
equality transports, strict associators, whiskered reservoir word comparisons,
zero-content beta/xi conjugations and functor images of these, hence an `eqToHom`:

* `tensorRowTargetIso_hom_eqToHom` (global path chart);
* `tensorContextIso_hom_eqToHom`, `tensorCrossContextIso_hom_eqToHom` (contexts);
* `tensorLayerDotIso_hom_eqToHom` (dot);
* `tensorLayerSameCrossIso_hom_eqToHom` (equal-colour crossing), via
  `homContentPostWordIso_zero_app_eqToHom` (the BB word comparison at content `0`);
* `tensorLayerCrossSourceIso_hom_eqToHom`, `tensorLayerCrossTargetIso_hom_eqToHom`
  (distinct-colour crossing).

The vacuum input-weight equivalence pulls `eqToHom` back to `eqToHom`
(`tensorHomEquivalence_preimage_eqToHom`), so chart changes between such charts are
equality transports (`TensorEntryPullback.chartChange_eqToHom_of`) and pulled-back
arrows are conjugate by equality transports (`TensorEntryPullback.arrow_eqToHom_conj_of`).

Layer coherence, with the literal layer maps retained:

* `tensorOriginalWordLayer_dot_transport`;
* `tensorOriginalWordLayer_sameCross_transport`;
* `tensorOriginalWordLayer_cross_transport`.

Each says: in global charts that are equality transports, the pulled-back literal
layer of the full chosen action equals the frozen local raw operator
(`tensorLayerDotRaw`, `tensorLayerSameCrossRaw`, `tensorLayerCrossRaw`), up to
equality transport of its endpoints.

## Remaining for `VacuumChartCoherence`

The `evaluation` field for general `f` still needs, for the chosen route bases
(`ChartField B Q` in `VacuumRouteFields.lean`): the observation-layer squares
matching the frozen raw operators with the coefficient operations, and the
induction over presented diagrams (identity case: the vacuum coefficient class).
