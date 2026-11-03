# Unit matrices at missing-colour output

For Brundan--Ellis (1.13), an output content γ with i absent has no lower
E/F summand. `ELVContentAbsentColour` proves that the actual global append
restriction of the full-content extension of any module N on γ is zero at
every word. Its induction coend and canonical shifted principal unit-family
coordinate are therefore zero. Off-diagonal Cartan signs give
`contentCrossingHeight_nonneg_of_not_mem`, including γ = [].

`FiniteZeroCoordinate.dropZeroPrincipalEquiv` drops precisely this proved-zero
coordinate, preserves the actual pointwise grading in both directions, and
leaves the other coordinates unchanged. Its `dropZeroPrincipalEquiv_columns`
identity identifies the resulting forward map with the remaining columns.

`ELVContentMissingColourMatrix.missingColourUnitMatrixIso` composes the inverse
of that coordinate equivalence with the GIVEN `contentUnitMatrixComponentIso`
on the full-content extension. `missingColourUnitMatrixIso_hom` identifies its
forward field with the finite assembly of the literal prescribed shifted
unit-dot columns, without a compatibility or inverse hypothesis. Its hom and
inv preserve the actual superspace grading. This closes the old global
missing-colour unit matrix, rather than only constructing a conjugate with an
unidentified forward field.

The paired consumers use a mixed-parity datum, output [!i] for each moving
colour i, and genuine empty output []. They apply the support/height lemmas,
drop/reinsert coordinates, identify the prescribed columns, check both inverse
laws and evenness, and audit all owned declarations against the established
axiom allowlist. The producer and consumer checks pass with pinned strict
settings: 22 support declarations, 15 coordinate declarations, and 13 matrix
declarations.

The ordinary scalar-probe missing-colour matrix still needs comparison of its
finite dotted columns and upper F/E chart with these given old columns. The
case γ = [] here is genuine empty output, distinct from an empty predecessor
with output [i]. The earlier scalar inverse candidates for output i::ν still
await identification of their principal and dotted fields through the content
charts; no such identification is supplied by this missing-colour result.
