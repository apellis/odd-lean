# Ground-valued last inverse row of the regular probe extension

The probe side of `SwappedVacuumNonpositiveBubbles.md`, §2, uses the
regular height-zero probe with its prescribed empty vector. Let N denote
this fixed-content module and J the full inclusion of empty content into
the old category. The canonical extension L is its existing balanced
induction along J.

`ProbeExtensionCoefficient.scalarUnit` inserts a ground scalar through
`probeVacuumScalarEquiv` and the literal inclusion unit. The inverse
`scalarCoordinate` uses the existing fully faithful unit inverse, followed
by the inverse empty scalar coordinate. Their composite on every scalar
is the identity (`scalarCoordinate_unit`).

For positive probe cutoff P, `functional` is the last coefficient row of
the prescribed old unit-matrix inverse, followed by `scalarCoordinate`.
Its domain is the literal full-old append coend on L. On every scalar c,
`functional_dot_window` proves

    functional(D^a(unit(scalarUnit(c)))) = if a + 1 = P then c else 0,

for every a < P. Here D is the original signed induction dot and unit is
the original ordinary append unit. The proof applies the existing inverse
matrix window; it does not assume a coefficient extractor or choose a
new polynomial presentation. In particular the last row is unrescaled.

The paired consumer uses the asymmetric two-odd-colour datum over the
rationals at probe levels one and two. It proves that this row is
surjective and exhibits a nonzero vector in each literal full-old append
coend with row value one. Thus the extraction statement is occupied.

The comparison with native fixed-content and ordinary scalar-probe coends,
the row's parity after these comparisons, its identification with a
prescribed normalized left probe cap, and the final mixed slide remain
separate obligations. No final swapped vacuum datum is asserted.
