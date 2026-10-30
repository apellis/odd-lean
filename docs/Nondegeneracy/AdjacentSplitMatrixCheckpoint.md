# Occupied adjacent split matrix

`adjacentSplit_braid` proves all four literal `i i j → j i i` braid entries
for arbitrary source and target paths at the endpoint with one repeated-colour
reservoir and two probes. It retains `c.IsInverse` and `CrossCoeffInputs`.
The J entry uses the actual Q-weighted rectangle; the square and conjugate
entries cancel only comparison isomorphisms. No crossing or Q factor is
inverted, and no transport identity is assumed.

The statement and its proofs are checked in `AdjacentSplitMatrix`,
`AdjacentSplitReduction`, and `AdjacentSplitBraid`.
`scripts/NonVacuity/AdjacentSplitMatrix.lean` applies the theorem at generic
occupied content and audits every declaration owned by those modules,
including private declarations, against `propext`, `Classical.choice`, and
`Quot.sound`. This is a supplied-data consumer, not an independently
constructed nonzero probe/reservoir representation.

## Remaining mathematical scope

Pure-probe and pure-reservoir adjacent-equal braids are proved separately.
Other mixed endpoint patterns, the actual repeated-outer polynomial
correction, complete `CrossBraid`, and nondegeneracy remain open.
