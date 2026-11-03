# The boundary inverse row on the literal power vacuum

`ELVPowerVacuumContentRows` supplies the remaining extension comparison in
`ContentVacuumCoefficientRows.md` for the coefficient lambda used in
`SwappedVacuumCoordinates.md`, §6.

The literal regular A/T vacuum vanishes on every nonempty word. Its
power-to-weighted descent retains these exact carriers, so
`weightedVacuum_contentSupported` proves support on content zero.
The existing `contentSupportedCounitIso` therefore recovers the given global
weighted vacuum from its canonical content-zero extension. Its forward map
is the literal full-inclusion counit, rather than an arbitrary isomorphism.

`contentVacuumTargetIso` composes the selected upper full-inclusion chart
with induction and restriction of that supported counit. It is a genuine
isomorphism from the canonical-content F/E value to the given global F/E
value restricted to empty content. The whole unit-column square, even-input
naturality of the given unit/dot columns, and the adjunction triangle prove
that this chart sends every prescribed column to precisely the prescribed
global column. Joint-epimorphism uniqueness then identifies the same inverse
coefficient rows as whole module maps.

For the literal power vacuum, `contentPowerVacuumCap_eq_inverseRow`
identifies the normalized cap with the final row of every inverse of the
given canonical-content boundary columns. The constructed absent-colour
inverse supplies these rows without an additional inverse assumption.
`contentPowerVacuumCap_functional` decodes the cap to the existing weighted
A/T-valued lambda. The existing `weightedFunctional_compare`, using the selected
`weightedTargetChart`, further compares this same weighted lambda with the
already prescribed old literal-T functional.
These statements apply to arbitrary F/E vectors, including odd coefficient
inputs, and introduce no new extraction functional or cap normalization.

The exact producer and occupied paired consumer pass strict scoped Lean
checks. All 101 owned declarations, including private and generated ones,
pass the standard axiom audit. The consumer uses cutoffs 4 and 5 on the
asymmetric all-odd datum and a surviving odd coefficient in the literal
power quotient. It identifies both normalized caps with the constructed
inverse rows, proves both caps nonzero, and applies the lambda identity on
every F/E vector. Full repository CI remains the integration gate.

This comparison identifies the boundary inverse cap on the actual regular
vacuum. The full swapped mixed inverse and bubble-series identification,
and extension to source-whiskered bubbles, remain separate obligations.
