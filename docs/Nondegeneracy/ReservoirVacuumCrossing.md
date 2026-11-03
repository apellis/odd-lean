# The zero-probe-content reservoir crossing

This supplies the distinct-colour reservoir-block comparison needed in
[SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §§2–6.

`reservoirVacuumPairIso` removes the two zero-content shifts and uses the
given postcomposition associator. `ProbeReservoir.reservoirVacuumCrossTargetIso`
first reverses the precise target-sector transport in `postCrossNe`, then
applies the target pair chart. Its source reservoir object is the given
object transported along the equality of the two formal-content endpoints;
no replacement-object equality is assumed.

`postCrossNe_reservoirVacuum` identifies the prescribed `postCrossNe` block,
through these source and target charts, with the literal reservoir factor
crossing left-whiskered by that transported Hom object. It is an equality
of entire Hom maps, including odd components and every input vector. It
uses the actual target-sector equality and its transport, and assumes
neither an action comparison nor faithfulness. The block formula itself
does not need a distinctness premise; identifying it with the distinct
branch of `crossImage` will use distinctness at the matrix attachment.

The paired consumer supplies a complete positive-level two-odd ELV factor
pair and both actual odd colours. Its Hom input is the identity at the
formal zero sector, with all step-validity and endpoint equalities proved.
The comparison is also applied to every Hom input at that endpoint. The
identity Hom has a nonzero odd exterior-coefficient input in the actual
lowest-weight regular-power family, proved using bounded coefficient
quotient injectivity. No separating-model or nonzero-crossing-output claim
is made.

Strict producer and consumer checks pass; all 17 owned declarations pass
the standard axiom allowlist.

The next matrix attachment must retain the source two-letter path's
endpoint cast, reduce the literal `crossImage` distinct branch to this
block, and combine its mapped square with `layerMap_reservoir_append`.
Transporting the two contexts through `reservoirWordFunctorIso`, applying
`TensorHomContexts.cross_apply`, and then using
`PowerWordLayerClasses.affine_class_square` provides the intended route to
the signed layer quotient square. Supported-family evaluation, complete
OLD probe relation data and the vacuum coefficient field remain separate.
