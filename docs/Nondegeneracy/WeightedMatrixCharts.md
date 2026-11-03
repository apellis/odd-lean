# The selected weighted matrix charts

DeformedMatrixComparison (2), (4) transports the prescribed matrix inverses
through the source and target of the ordered mate square. The comparison
maps in that square need genuine inverses, without a supplied invertibility
hypothesis.

`weightedAppendLinearEquiv` evaluates the selected five-isomorphism append
comparison. Its forward map is exactly `weightedAppendComparisonLinear`.
`weightedMateTargetLinearEquiv` is this equivalence at the appended old output
word, matching the target map in `appendWeightedModuleIso_hom_mate`.

The source uses the genuine inverse restriction-square isomorphism.
`inducedMapIsoLinearEquiv` applies the existing induction functor to this
isomorphism. Its parity-zero component is the literal `mapComponent` when
the input isomorphism is even. `weightedMateSourceLinearEquiv` then composes
this induced equivalence with the selected append equivalence on the
restricted truncated module. `weightedMateSourceLinearEquiv_hom` identifies
its forward map with the exact `weightedAppendSourceLinear` of the mate square.

The paired consumer instantiates the mixed-parity datum, both moving colours,
both inverse products of each chart, and the appended unit tensor of the
vacuum representable. These are the charts used by the subsequent component
matrix transport; equality of every truncated finite matrix entry and its
transported inverse is a separate obligation.
