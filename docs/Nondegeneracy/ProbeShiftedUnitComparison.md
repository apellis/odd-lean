# Prescribed scalar unit columns with canonical parity sources

Source: DeformedMatrixComparison (1), (4), and the canonical shifted finite
families implementing Brundan--Ellis (1.13)--(1.14).

`shiftedUnitDotColumn` uses the existing canonical source parity-coordinate
map followed by the actual `unitDotColumn`. Its raw component is exactly
`shiftedUnitDotLinear`, and it is even. The endpoint variant uses the given
`endpointUnitDotLinear` to retain the literal output-object transport.

The source-coordinate square is evaluated by
`parityRestrictionIso_hom_coordinate_total`.
`shiftedUnitDotLinear_compare` transports an unshifted column equation
through this full canonical parity/restriction module isomorphism.

For the scalar probe, the original chosen `probeAppendComparisonLinear`
intertwines the prescribed signed dot and all its powers. The literal
append-unit calculation then gives
`probeAppendComparisonLinear_unitDotColumn` for every power, followed by
`probeAppendComparisonLinear_shiftedUnitColumn` on the actual canonical
shifted sources. No extra generator-compatibility premise or column
rescaling is introduced.

`unitMatrixEntry_some_eq_shiftedUnitDotColumn` binds the generic column
literally to the existing old finite unit-matrix field. In particular it
also applies to old representables without imposing a scalar-evaluation
hypothesis on those representables.

Strict producer and consumer checks pass. The consumer covers mixed
even/odd colours, all powers, vacuum, the given module components and
evenness, and the old representable field binding. It audits all 57 owned
declarations against the repository axiom allowlist.

Together with the shifted cap batch, this establishes the dotted matrix
slots under the scalar charts. The first mate slot and the full finite
inverse assembly remain separate obligations.
