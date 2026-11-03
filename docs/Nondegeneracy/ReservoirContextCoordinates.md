# Both reservoir contexts in word coordinates

This connects the literal reservoir matrix entries to their two word
contexts in [SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §§2–6.

`ProbeReservoir.reservoirContextIso` applies the existing even
`reservoirWordFunctorIso` to the right path value, whiskers that comparison
by the unchanged intervening factor 1-morphism, and applies the left path
comparison. Its target is the right reservoir word, then the intervening
factor, then the left reservoir word. Each word retains the established
right-to-left reading convention. `reservoirContextIso_hom_mem` proves
that the resulting chart is even.

`reservoirContext_square` proves that a factor map inside both actual
path contexts becomes its literal left and right word whiskering in this
chart. The factor map may be inhomogeneous. The proof uses the even-left
interchange law for the right chart, followed by naturality of the left
path comparison. Thus no new sign, parity premise on the factor map, or
independently supplied generator comparison is needed.

`reservoirLayerDotWordIso` and `reservoirLayerSameCrossWordIso` compose
these context charts with the existing literal middle-strand charts.
`layerMap_reservoir_dot_word` and `layerMap_reservoir_cross_same_word`
start with the actual `layerMap (P.upwardGens a)`, at its selected
reservoir output path, and identify the output in the two-word chart
with the arbitrary input entry in that chart followed by the prescribed
two-whiskered factor dot or equal-colour crossing. The factor maps, signs,
matrix sums, and append transports are unchanged.

The statements require a supplied complete `ProbeReservoir`. Both outer
paths are upward at probe content zero, and the input matrix is arbitrary.
No inverse property for the mixed coefficient, complete relation assertion
for the generator record, or faithfulness of evaluation is assumed.

The paired consumer supplies a complete positive-level two-odd ELV
factor pair. It uses two nonempty contexts and supported identity entries
at the selected three-letter dot path and four-letter equal odd crossing
path. It also applies both matrix formulas to arbitrary input families,
checks chart evenness, and tests the generic square on every factor
endomorphism and on the inhomogeneous map `dot + id`. It does not assert
that the identical factors form a separating model or that these matrix
entries are nonzero. The separate nonzero mixed and two-odd full-coefficient
vector calculations are in `ELVTensorHomContexts` and `PowerWordLayerClasses`.

Strict producer and consumer checks pass; all 13 owned declarations pass
the standard axiom allowlist.

For the quotient-square attachment, specialize to the unchanged chosen
ELV reservoir and tensor vacuum. The two word contexts now correspond
to the prescribed append contexts in `TensorHomContexts`; the pair
associator in the crossing chart is the prescribed factor-word comparison.
The resulting physical OLD operator is identified with the coefficient-one
original affine layer by `ContextualOldGenerators`, and
`PowerWordLayerClasses.affine_class_square` gives its output quotient class
on every vector with the specified input class. This route does not infer
faithfulness of evaluation at the regular probe.

The distinct-colour word-context attachment still must reindex the actual
right path along the equality of its two formal-content endpoints before
applying these context charts. Supported-family evaluation, complete OLD
probe relation data and the vacuum coefficient field remain requirements
before constructing `VacuumCornerEvaluation`.
