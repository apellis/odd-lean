# Weighted finite matrix components

DeformedMatrixComparison (2), (4) needs the prescribed matrices on the
coefficient quotient in the canonical parity coordinates of
Brundan–Ellis (1.13)–(1.14).

`ELVWeightedMatrixComponents` defines `weightedUnitMatrixFamily`,
`weightedCapMatrixFamily`, their entries and the finite row/column
assemblies. The entries use the given ordered cup-crossing-cap mate,
ordinary unit and counit, and unscaled dot powers. The canonical parity
isomorphisms are inserted on the prescribed sides. A private matrix datum
fixes the module endpoints before assembling their shifted coordinates;
it introduces no additional hypothesis.

`weightedMatrixMate_mem`, `weightedUnitMatrixEntry_mem`,
`weightedCapMatrixEntry_mem`, `weightedUnitMatrixComponent_even` and
`weightedCapMatrixComponent_even` prove the required degrees. The public
`*_Entry_none` and `*_Entry_some` equations identify the literal shifted
entries. `BalancedInduction.inductionMatrixMate_apply` evaluates the mate
as the given ordered component on every coend vector, retaining its minus
sign and original crossing parameter. The generic crossing-family and
ordered-mate degree lemmas support these constructions.

`weightedMatrixMateValue` retains the source and target module values.
`weightedMatrixMateValue_eq_total` identifies it with the prescribed total
component. `BalancedInduction.inductionMatrixMate_value_apply` identifies
that evaluation with the raw ordered mate before choosing the append
functor. These equations are used in the chosen matrix-chart comparison;
they impose no compatibility premise.

The four `inductionUnitMatrixEntry_*_total` and
`inductionCapMatrixEntry_*_total` formulas evaluate the actual shifted
fields as the prescribed raw mate, unit/dot and dot/counit maps before
choosing an append functor. They support the finite field comparison.

The producer and paired mixed-colour/vacuum consumer pass the pinned
strict checks, including the allowlist audit of every owned declaration.
No inverse of the quotient component matrices is claimed here. The next
step is their exact finite coordinate square with the already constructed
arbitrary-module old matrix inverses.

The datum-level mate also retains input-module signed naturality.
`orderedMateComponent_supernatural` keeps the negative flattened crossing;
`inductionMatrixMate_supernatural` attaches that family to the chosen datum
before quotient specialization. It supplies the principal fields in the
natural transformations of `ELVWeightedMatrixFunctor`.
