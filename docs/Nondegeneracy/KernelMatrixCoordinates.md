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

Strict producer/consumer checks pass. The consumer uses actual mixed odd/even
rational data, reversed old-word endpoints and zero/three finite coordinates,
and audits all eleven owned declarations against the three allowed axioms.
Full repository CI remains the integration gate.

The all-content positive/negative matrix conjugations and arbitrary-module
inverse remain open. The previous generic pointwise row wrapper repeatedly
exceeded normalization limits; it is not needed by this bundled interface.
Comparisons with the representable inverses must retain exact word endpoints,
ordinary-right source actions and the prescribed cap/unit normalizations.
