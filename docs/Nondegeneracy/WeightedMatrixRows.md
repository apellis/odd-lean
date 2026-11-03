# Weighted dotted matrix rows

DeformedMatrixComparison (2), (4) uses the ordinary unit followed by each
given dot power and each dot power followed by the ordinary counit.
`oldUnitColumn_eq` and `oldCapRow_eq` identify the given old module maps with
the generic ordinary-adjunction constructions. `truncatedModuleDot_eq`
identifies their target dot with the prescribed module-induction generator.

The constructions `unitDotColumn` and `capDotRow` have the expected degree
and their total components are `unitDotLinear` and `capDotLinear`.
`endpointUnitDotLinear_total` retains the canonical equality of the two
appended output objects; it transports the given module column, without
rescaling it. These comparisons are proved before the append functors and
module carriers are specialized.

`weightedAppendSourceLinear_dot` and its power theorem retain the full signed
dot under the exact input-module comparison. The induced genuine restriction
isomorphism and the checked counit square prove
`weightedMateSourceLinear_counit`. Consequently
`weightedMateTargetLinear_unitDot` compares every prescribed unit/dot column,
and `weightedMateSourceLinear_capDot` compares every prescribed dot/counit row.
Neither headline assumes any row equality or comparison invertibility.

The paired consumer uses the mixed-parity and vacuum representables, both
moving colours, arbitrary powers, the exact old module-row identifications,
and the target module-induction dot. Combined with the checked mate comparison,
these are the forward-entry identities needed for finite matrix transport.
Assembly through the canonical finite parity coordinates and the resulting
component matrix inverses remain separate.
