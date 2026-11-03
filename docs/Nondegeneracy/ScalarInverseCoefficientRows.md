# Scalar transport of inverse unit coefficients

The normalized left cap in DeformedMatrixComparison is a specified inverse
unit-matrix coordinate followed by its canonical source unshift. It is
separate from the ordinary right counit and the dotted right-cap rows.

`MatrixInverseTransport` proves forward-to-inverse square cancellation and
coordinate transport through common charts, before substituting coend
carriers. `ELVUnitColumnInverseRows.unitColumnUnshift` projects to the exact
r-th shifted value coordinate and removes the original shift.
`unitColumnInverseRow` applies this to a GIVEN matrix inverse. Its degree is
r*p whenever that inverse is even. `unitColumnInverseRow_compare_common`
transports the specified unshifted inverse row through two proved forward
matrix squares; its intermediate square premises are supplied in the concrete
application, rather than assumed as new compatibility hypotheses.

`ELVProbeUnitInverseRows.probeMissingColourUnitCoefficient` is the actual
ordinary missing-colour unit-matrix inverse coefficient with this original
unshift. `_mem` gives its prescribed degree. `_compare` proves that every
coefficient is preserved through the same selected content/scalar F/E and
value charts, including genuine empty output. The old side uses the GIVEN
old matrix inverse after the proved-zero principal slot is dropped; the
ordinary side uses the inverse whose forward field is already identified
with the literal ordinary unit columns. Both forward-square premises are
proved from the existing chosen-chart theorems.

All three producers and the paired concrete consumer pass strict pinned
checks. All 63 owned declarations pass the established axiom audit (8 inverse
square, 13 canonical-row, 42 scalar coefficient declarations). The consumer
uses mixed regular scalar modules, both moving colours, all coefficient
indices, proved existing top rows, genuine empty output, and the top row's
actual even/odd parity. No right counit is substituted for an inverse row.

Literal attachment of the old side to `contentUnitCoefficientMap` and its
empty-output `moduleUnitCoefficient` normalization is supplied by
`ELVProbeLeftCapComparison`; see `ScalarLeftCapBinding.md`. Binding the native
relative cap map, the final mixed left-cap datum, its module naturality, and
the representation/nondegeneracy theorem remain separate from this component
inverse-row comparison.
