# Distinct-colour factor crossings in reservoir matrices

This supplies the distinct-colour matrix-to-factor step in
[SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §§2–6.

`ProbeReservoir.reservoirCrossSourceIso` retains the actual terminal cast
of the source two-letter path. `reservoirCrossTargetIso` retains the
target path and reverses precisely the target-sector transport in the
prescribed reservoir crossing. `crossImage_reservoirVacuum` proves that
the literal distinct branch of `crossImage`, in these two charts, is the
original reservoir factor crossing. The comparison is proved with the
existing `twoTwo_two_heq` path formula and
`postCrossNe_reservoirVacuum`; no comparison is supplied as a premise.

`reservoirLayerCrossSourceIso` and `reservoirLayerCrossTargetIso` extend
these charts through both actual outer path functors and their append
equalities. `layerMap_reservoir_cross_ne` starts with the existing literal
`layerMap (P.upwardGens a)`. At the selected reservoir path, its output
followed by the target chart equals the arbitrary input entry followed by
the source chart and the left path functor applied to the original
factor crossing. The right path value is transported along the original
equality of formal sector endpoints; it is not replaced by an assumed
equal reservoir object.

The theorem is an equality of whole Hom maps, including every parity
component and every input vector. It assumes a supplied complete
`ProbeReservoir`, distinct colours, and an upward right path ending at
probe content zero. The left path and input matrix are arbitrary. No
inverse property for the mixed coefficient, relation assertion for the
generator record, or faithfulness premise is needed.

The paired consumer supplies a complete positive-level two-odd ELV
factor pair, two nonempty contexts and a crossing of the two odd colours.
It constructs all four step-validity proofs, the source endpoint cast,
and a supported input matrix with an identity transport at the selected
four-letter path. It also applies the square to every input matrix in
that fixture. It asserts neither a separating-model property nor that
this matrix entry is nonzero. Nonzero mixed and two-odd vector tests for
the physical contextual factor maps and their quotient classes occur in
`ELVTensorHomContexts` and `PowerWordLayerClasses`.

Strict producer and consumer checks pass; all 20 owned declarations pass
the standard axiom allowlist.

Together with `ReservoirLayerGenerators` and `ReservoirLayerCrossings`,
this identifies the prescribed factor generator in each surviving
upward dot or crossing matrix entry, retaining both contexts. The next
attachment transports the left path functor by
`reservoirWordFunctorIso` and the right path value by its even comparison.
The chosen tensor-Hom context charts then give the physical OLD map, and
`PowerWordLayerClasses.affine_class_square` supplies its signed source
quotient class. Supported-family evaluation, complete OLD probe relation
data and the vacuum coefficient field remain separate requirements for
`VacuumCornerEvaluation`.
