# Parity of the extended regular-probe inverse row

The last inverse row in the probe normalization of
`SwappedVacuumNonpositiveBubbles.md`, §2, has degree `(P-1)p`.
`ProbeExtensionCoefficient.functional_mem` proves this for the literal
ground-valued row on the canonical full-old regular-probe extension.

`extension_empty_even` proves that every vector of the extension's empty
component is even. Its fully faithful inclusion unit is surjective and
even, and the original regular probe's empty component is entirely even.
Consequently `scalarCoordinate_mem` shows that scalar decoding is even.
Composing this decoder with the prescribed inverse coefficient row retains
that row's degree, with no parity shift or scalar rescaling added.

For an odd colour the prescribed positive probe cutoff is `P=2m`, so this
row is odd. The paired rational two-odd-colour consumer uses levels one
and two and exhibits a nonzero odd coend vector on which the row is one.
Thus its oddness is tested on an occupied odd component of the original
full-old coend, rather than a zero map or a separate model.

Comparison with fixed-content and ordinary scalar-probe coends, the
identification with a prescribed normalized left probe cap, and the final
mixed slide remain separate obligations. This result does not assert a
swapped vacuum datum.
