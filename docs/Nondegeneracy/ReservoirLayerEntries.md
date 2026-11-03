# Literal layer matrices at reservoir paths

This supplies the unique-path matrix step in
[SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §§2–6, after the
chosen generator comparisons in
[ELVTensorHomContexts](ELVTensorHomContexts.md).

`ProbeReservoir.layerMap_reservoir` starts with the existing literal
`layerMap`, for an upward input boundary and a right endpoint of probe
content zero. Its input-path sum is exactly the selected input coefficient
followed by the existing `compLayer`. The input coefficient is arbitrary;
no vanishing or coordinate-comparison assumption is imposed on it.

`layerMap_reservoir_append` uses an explicitly split output path
`pu · pg' · pv`. If the generator's input word and the right whisker are
upward, and the final probe content is zero, then the actual layer map is
exactly `layerEntry` for the supplied input middle path `pg`. Thus both
whiskers, the given generator image, and every path-append equality
transport in `layerEntry` remain unchanged. The proof first deduces that
the middle endpoint has probe content zero, then collapses the existing
middle-path sum by `VacuumPaths`.

These are generic theorems about a supplied complete `ProbeReservoir` and
its existing generator record. They do not construct the intended OLD
probe record, supply a missing relation field, or assert faithfulness of
evaluation at a regular probe.

The paired consumer supplies a complete ELV factor pair with both factors
equal, positive cutoff and the actual highest-weight pairing. It constructs
supported `Ys` and `Gs`, and an input matrix with the identity transport
at a nonempty reservoir path and zero entries elsewhere. Both formulas
are applied to the literal dot layer with its canonical `dotImage`; the
whole-domain formula is also applied to an arbitrary input family. Other
fields of this consumer's generator record are zero, with no assertion
that this record satisfies the presentation relations. No separating-model
claim or nonzero-vector claim for this matrix fixture is made. The
occupied mixed and two-odd coefficient-vector tests for the actual chosen
outer-context maps are in `ELVTensorHomContexts`.

The producer and consumer pass strict scoped checks; both owned
declarations pass the standard axiom allowlist.

For the intended observation, assemble the actual OLD probe into its
chosen record, use the supported `Gs`/`Ys` described in
[ELVTensorHomEntries](ELVTensorHomEntries.md#remaining-attachment-to-the-literal-layer-action),
and transport this literal `layerEntry` through the reservoir
`pathFunctor` comparisons. The two-whisker square in
`ELVTensorHomContexts` then evaluates its chosen generator. The
relation-derived action is attached by
`SwappedRelationData.upwardModuleAction_act_layer`. Identification with
the signed quotient class and the vacuum coefficient value remain before
constructing `VacuumCornerEvaluation.ev_layer` and `ev_vacuum`.
