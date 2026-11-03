# Equal-colour crossings in reservoir matrix entries

This supplies the equal-colour crossing matrix-to-factor step in
[SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §§2–6, alongside
the dot comparison of [ReservoirLayerGenerators](ReservoirLayerGenerators.md).

`ProbeReservoir.reservoirLayerSameCrossIso` composes the literal
path-append equality with the prescribed `homContentPostWordIso` for the
middle two reservoir strands. Both outer path functors are retained.

`layerMap_reservoir_cross_same` identifies the actual surviving entry of
`P.layerMap (P.upwardGens a)` with the left path functor applied to
`Z ◁ P.W.cross i i`, after this chart. Here `Z` is the actual right path
value, and the input matrix is arbitrary. The proof computes the
reservoir block of the existing crossing image, then cancels its word
comparison with the chart. It assumes neither a generator comparison nor
faithfulness of regular-probe evaluation. All factor parity and crossing
sign conventions are unchanged.

The theorem requires a supplied complete `ProbeReservoir`; it does not
construct the intended OLD probe. The right path is upward and ends at
probe content zero. The mixed coefficient is used only as the argument
of the prescribed generator record, without an inverse or relation
assertion.

The paired consumer constructs a complete positive-level two-odd ELV
factor pair. It supplies two nonempty contexts, an equal odd crossing, a
supported identity transport at the selected four-letter path, and also
an arbitrary input matrix. This verifies the stated complete-factor
premise. It asserts neither a separating-model property nor nonvanishing
of the matrix entry. Nonzero full-coefficient vector calculations for the
corresponding contextual factor crossing and its signed quotient class
are supplied by `ELVTensorHomContexts` and `PowerWordLayerClasses`.

Strict producer and consumer checks pass; all seven owned declarations
pass the standard axiom allowlist.

The remaining attachment to `VacuumCornerEvaluation.ev_layer` transports
both path contexts through `reservoirWordFunctorIso`, applies the chosen
tensor-Hom context chart, and then uses
`PowerWordLayerClasses.affine_class_square`. The distinct-colour crossing
requires its separate target-sector transport comparison. Supported-family
evaluation, the complete OLD probe relations and the vacuum coefficient
field remain separate requirements.
