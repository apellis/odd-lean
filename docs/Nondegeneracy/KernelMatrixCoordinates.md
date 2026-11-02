# Canonical coefficient-kernel coordinates

DeformedMatrixComparison section 4 requires comparison of the ordinary-right
coefficient kernels with the prescribed representable matrix inverses.

`ELVKernelMatrixCoordinates` supplies `kernelSourceCoordinates`,
`positiveKernelCoordinates` and `negativeKernelCoordinates`, together with
coordinate projection formulas. The positive family retains its IndRes kernel
and finite identity-Hom coordinates; the negative family retains its upper Hom
and finite identity-Hom coordinates. The empty finite family is included.

`actualMateKernelLinear_eq_row` identifies the literal coefficient map with
`kernelMateRowLinear` as a bundled linear map at identical kernel endpoints.
The latter is exactly the prescribed `matrixMateRow` composed with the canonical
source coordinates. No assumed inverse, field, finite-colour or flatness input
is introduced.

Full build, axiom audit and concrete consumers passed in #950; the coordinate prerequisite is integrated. The consumer uses actual mixed odd/even
rational data, reversed old-word endpoints and zero/three finite coordinates,
and audits all eleven owned declarations against the three allowed axioms.


The coefficient-matrix transfer is implemented in `ELVKernelMatrixBijective`.
For each moving parity and height sign, the literal list-endpoint coordinates
conjugate the coefficient map to the verified representable finite matrix.
The comparison keeps mate and cap operators folded and compares only their
arguments. Abstract parity elimination combines the two moving parities
without expanding the coefficient maps during subtype conversion.

`actualPositiveKernelMap_bijective` and
`actualNegativeKernelMap_bijective` use the target-content unit/cap count
at every old source. Matching content uses the representable inverse;
different content uses the verified zero-component matrix theorem.
No inverse hypothesis, flatness, field or finite-colour premise is added.

Strict producer, concrete consumer and umbrella-export checks pass. The consumer
uses mixed rational data, reversed matching-content words and off-content empty
words for both height signs and audits all 25 owned declarations.
Full repository CI remains the integration gate.
Arbitrary-module inversion remains separate: tensor these coefficient
isomorphisms and use the verified whole forward-map identifications and
matrix evenness.
