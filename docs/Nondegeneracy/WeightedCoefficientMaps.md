# Weighted inverse coefficients as canonical-content module maps

`ELVWeightedCoefficientMaps` upgrades the normalized weighted inverse row
of `SwappedVacuumCoordinates.md`, §6, to an actual homogeneous module map
on its canonical output content. It projects the given
`weightedContentUnitMatrixIso.inv` and removes exactly the original source
parity shift. Its degree is `r*p`; its output-endomorphism naturality has
the corresponding Koszul sign, including on odd coefficient arrows.

At genuine empty output, the inverse component equals the actual
`weightedUnitMatrixComponentIso.inv`. The proof identifies their given
forward fields and uses isomorphism uniqueness. Hence
`weightedContentCoefficientMap_vacuum_total` is exactly
`weightedUnitCoefficient`, with no added inverse premise or cap scalar.

For the literal power vacuum, `PowerVacuumCoefficient.weightedCoefficientCap`
is this actual canonical-content module map. It has degree `(cutoff i-1)*p`.
`weightedFunctional_coefficientCap` identifies its empty component, decoded
through the original typed weighted empty coordinate, with the previously
checked A/T-valued `weightedFunctional`. This retains the actual
power-to-weighted comparison and does not replace A/T by a weighted regular
quotient.

The exact producer and paired consumer pass strict scoped Lean checks.
The consumer uses colour cutoffs 4 and powers 4, with upper weight bound 39.
It proves the actual cap is odd and nonzero, and extracts both surviving
independent odd coefficient classes from its prescribed top unit/dot
vectors. Extraction holds on every A/T coefficient vector. All 44 owned
declarations, including private and generated declarations, pass the standard
axiom audit. Full repository CI remains the integration gate.

The source and target here are canonical restrictions of the global weighted
F/E module and original module. Attachment to the chosen native content/weight
inverse row still requires its given finite chart square. A complete mixed
swapped `s/u/v/x/y` datum and slide relation remain separate obligations.
