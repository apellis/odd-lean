# Canonical point charts on shifted matrix families

Source: DeformedMatrixComparison (4), (5), as needed by the prescribed
finite unit/cap matrix comparisons.

`shiftedModuleValueLinearEquiv M N w v e q` removes the actual canonical
module parity coordinate on the source, applies the selected plain value
chart `e`, and inserts the actual canonical target coordinate. The modules
can belong to different categories and be evaluated at different objects.
Neither their module actions nor their parity structures are replaced.

The exact chain and both coordinate squares are public. An even selected
plain chart gives even forward and inverse shifted charts. A finite family
can therefore use these point charts with `LinearEquiv.piCongrRight`,
including the literal `Option (Fin m)` matrix indexing.

Strict producer and paired consumer checks pass. The consumer applies the
APIs to the actual scalar old/ordinary module comparison on mixed colours,
both shifts, the whole Option/Fin family, and vacuum. It audits all eleven
owned declarations against the repository axiom allowlist.

These are genuine invertible coordinate charts. Matrix-entry comparison
and matrix invertibility are subsequent obligations, rather than premises
or conclusions of the chart construction.
