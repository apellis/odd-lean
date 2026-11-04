# Coefficients on the whole supported matrix module

`SupportedSectors.tensorMatrixCoefficientAction` is an algebra map from
the full original `SYM D k` ring to the endomorphisms of the actual
supported matrix module with `tensorSourceFamily` and
`tensorTargetFamily`. It retains every source sector, weighted target
sector and formal path. At each component it is the existing
`tensorFamilyWordHomCoefficientAction`.

`tensorMatrixCoefficientAction_apply` gives its literal formula:
postcompose the same matrix entry with
`tensorFamilyPathCoefficientAction` on that path's same target object.
There is no change of row source or target, no homogeneous-coefficient
restriction and no reversal of source multiplication. The construction
assembles the dependent products of the pointwise algebra maps.

The consumer uses the actual nonzero two-letter matrix vacuum for a
two-odd datum with a root-weight collision. The mixed-parity coefficient
`1 + delta` acts nontrivially: its source-ring inverse is `1 - delta`,
since `delta² = 0`, and the induced algebra action therefore cannot kill
the nonzero vacuum. The component formula is also applied at arbitrary
matrix indices and full coefficients.

The canonical-observation compatibility still requires transport of
this supported matrix action through `tensorRowTargetIso` and
`TensorEntryPullback.map_square`. The independent path/global chart
coefficient square supplies the target-side evaluation, but does not
by itself identify this whole matrix action under the original-row
pullback.
