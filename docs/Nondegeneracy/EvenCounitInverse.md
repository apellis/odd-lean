# Even ordinary dotted-counit inverse

This transports the negative-height raw matrix of
[DeformedRouquierMatrix §4](DeformedRouquierMatrix.md) through the canonical
even source comparison required by
[DeformedMatrixComparison §4](DeformedMatrixComparison.md).

`evenCounitMatrixEquiv` is a linear equivalence from the existing ordinary
Ind–Res representable component to the prescribed upper Hom and finite
old-Hom cap coordinates. It composes canonical J, the proved raw even
matrix and negation of the entire output. The raw cap rows are minus the
ordinary dotted counit by `evenCapRow_normalization`, so this final
invertible row change makes every cap row the ordinary counit.

`evenCounitMatrixEquiv_fst` identifies its first row as minus the literal
balanced crossing after J. `evenCounitMatrixEquiv_cap` identifies every
other row with the ordinary counit after the actual induction-dot power.
No coefficient elimination is repeated, and full exterior coefficients
are retained. The ordered categorical mate identity remains separate;
this result does not assume it.

The strict source and consumer pass, including all nine owned-declaration
axiom checks. The concrete consumer uses mixed even/odd colours,
arbitrary old endpoints with three cap coordinates, checks both inverse
products and every cap row, and includes height zero with no cap
coordinates. Full CI is required before integration; see
[STATUS](STATUS.md).
