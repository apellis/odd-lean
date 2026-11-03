# Empty-content inverse coefficient rows

`ELVContentVacuumCoefficientRows` attaches the coefficient row in
`SwappedVacuumCoordinates.md` to the inverse of the given canonical-content
unit/dot columns at the empty-content boundary of BE (1.14).

`weightedContentCoefficientMap_unitDotColumn` first proves the Kronecker
window as an equality of whole module maps for every weighted input module.
It uses the prescribed weighted inverse row, its empty component formula,
and the given typed unit/dot column. It applies to all coefficient vectors.

For a content-zero module `M`, `contentVacuumCoefficientMap` is the composite
of the selected upper full-inclusion chart, the weighted coefficient row
on the canonical extension of `M`, and the inverse selected value chart.
The existing whole unit-column chart square gives exactly the same
Kronecker window for the literal canonical-content columns.
`contentVacuumCoefficientMap_eq_inverseRow` then applies the joint-epimorphism
identity of `SuperSumInvFrom`: every inverse of these prescribed columns
has this row. The absent-colour inverse already supplies such an inverse,
so no finite-matrix-isomorphism reconstruction or inverse premise is added.
Its homogeneous degree is exactly `r*p`, derived from that literal inverse.

The paired consumer uses an asymmetric all-odd two-colour datum with
reservoir cutoffs 4 and 5 and the literal elementary-power quotient with
powers 4. A surviving odd coefficient occupies the content-zero module.
Both prescribed top rows are nonzero, equal the constructed boundary
inverse rows, and obey the whole-module column window. The odd-cutoff
case retains its even top-row degree; no even-cutoff restriction is used.

The exact producer and paired consumer pass strict scoped Lean checks. All
63 owned declarations, including private and generated declarations, pass
the standard axiom audit.
Full repository CI remains the integration gate.

The weighted row here is evaluated on the canonical extension of `M`.
Identifying this extension chart with the separately given global regular
power vacuum is a further comparison; it is not inferred merely because
the content-zero restrictions agree. The complete swapped mixed-inverse
and bubble identification also remains separate.
