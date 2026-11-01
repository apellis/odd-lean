# Even ordinary-source positive inverse

The positive profile of
[DeformedMatrixComparison §4](DeformedMatrixComparison.md) uses canonical
even J and the actual ordinary adjunction unit followed by induction-dot
powers. Its ordered categorical mate attachment is in [ActualMatrixFamilies](ActualMatrixFamilies.md).

`evenUnitDotPolynomialMap` is the finite sum of the actual ordinary
`inductionUnitDotColumn` maps. For an even moving colour the generic
dot-power scalar is one, so `evenUnitDotPolynomialMap_eq` identifies this
unscaled sum with the literal output-polynomial map from
[UnitDotColumns](UnitDotColumns.md).

`evenUnitPositiveMatrixEquiv` transports the raw positive inverse through
canonical J, negating its crossing source only.
`evenUnitPositiveMatrixEquiv_apply` identifies it as minus crossing after
J plus this unscaled ordinary unit/dot polynomial assembly. No parity
projection, column equality premise or further elimination is assumed.

Strict source and concrete mixed-colour consumer pass, with all fourteen
owned-declaration axiom checks. The consumer checks both inverse products,
the entire map, each ordinary column at arbitrary row index, and the exact
polynomial window with four coefficient slots. The producer and concrete
consumer were integrated with the full-CI verified representable inverse
closure in [#889](https://github.com/apellis/odd-lean/pull/889), including the
global axiom audit and non-vacuity checks. See [STATUS](STATUS.md) for the
remaining arbitrary-module transfer.
