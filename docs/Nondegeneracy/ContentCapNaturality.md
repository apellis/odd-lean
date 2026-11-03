# Input-module supernaturality of the inverse coefficient cap

`ELVContentCapNaturality` proves that the prescribed inverse-unit coefficient
row and the selected native coefficient cap are homogeneous supernatural
families in their input module. If the row has degree `r*p` and the input
map has parity `q`, the naturality square has the scalar
`(-1)^((r*p)*q)`. Naturality is not restricted to even input maps.

The proof uses `contentUnitMatrixFunctorNatIso` on all old input modules,
restricted only in its output content. Its inverse is natural also when
that output content is empty. Coordinate projection is even; the original
source parity unshift contributes exactly the displayed Koszul sign.
The selected native F/E chart and inverse fully faithful inclusion unit
are even natural comparisons. No `i::ν`-only grid inverse is substituted
at empty output.

Public declarations:

* `contentUnitCoefficientMap_supernatural` for the global-old input family;
* `contentCoefficientCap_supernatural` for the given native F/E cap;
* `contentCoefficientCapFamily`, with its exact row degree and total
  component equal to the already checked fixed-input cap.

The producer and paired consumer pass strict scoped Lean checks, and all
29 owned declarations, including private and generated declarations, pass
the standard axiom audit. The consumer uses the actual regular empty probe
at positive odd-colour cutoffs 2 and 4 and its canonical nonzero odd shift
comparison. The signed cap square has a nonzero negative side; the unsigned
square is proved false over ℚ. It also checks that family evaluation gives
exactly the existing native cap on arbitrary input modules.

This closes the input-module family obligation recorded in
[ContentCoefficientCaps](ContentCoefficientCaps.md). Full repository CI
remains the integration gate. A final mixed swapped action and its slide
relation are separate obligations.
