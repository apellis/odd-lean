# The signed crossing on iterated weighted induction

DeformedMatrixComparison (2), (4) uses the given `signedEqualInductionCross`,
constructed from the old adjunction and the canonical induction flattening.
Its component at the prescribed degree descends as
`weightedSignedDoubleCrossing`. No arbitrary crossing map is substituted.

`pairWeightedModuleIso_crossing` promotes the checked raw-coend comparison
to equality of the given module morphisms. `weightedDoubleCrossing` is the
descent of `equalCrossOnDoubleInduction`; `truncatedDoubleCrossing` uses the
same canonical truncated flattening and the existing appended `crossTwo`
generator identified in `WeightedAppendCrossing.md`.

`doubleWeightedModuleIso_crossing` proves the resulting conjugation square
on the selected iterated isomorphism. `doubleWeightedModuleIso_signedCrossing`
retains the exact old signed component and the target's extra minus.
The paired consumer applies these identities to both moving parities and
the mixed and vacuum representables, and checks the odd crossing sign.

These are crossing comparisons. Transport of the ordered cup-crossing-cap
mate and the prescribed inverse matrix remains separate.
