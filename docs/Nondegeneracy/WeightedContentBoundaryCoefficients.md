# Boundary coefficients at arbitrary stored content

`ELVWeightedContentKernelBoundaryCoordinates` completes the formal-content
transport needed for the weighted finite-window contractions of
`SwappedHomInversion.md` §4 (7).

`weightedContentUnitBoundaryCoefficient` and
`weightedContentCapBoundaryCoefficient` retain the raw OLD source
endomorphisms at arbitrary stored content. A dependent content recursion
transports the object, the height condition and its finite coordinate
count together. Its beta rule is proved generically, before specializing
to inverse-valued coefficient families.

`weightedContentUnitBoundaryValue_evaluate` and
`weightedContentCapBoundaryValue_evaluate` identify the literal chosen
weighted `g'` contractions with the action of those source coefficients
on every module vector. Their corresponding coefficient `_degree`
theorems prove degrees `2 dᵢ(r-j)` in both orientations, for every finite
`j` and arbitrary ordinary dot power `r`.

The producer and paired
`scripts/NonVacuity/ELVWeightedContentKernelBoundaryCoordinates.lean`
consumer passed Lean 4.34.1 with warnings as errors, both repository
compatibility options and default limits. The consumer audits all 34
owned declarations against the three allowed axioms. Both moving
parities, both height orientations and every finite coordinate are
exercised with separately stored formal contents and their equality
proofs. Unit windows have sizes 8 and 10; cap windows have size 1.

No chosen weight/reservoir boundary degree or coefficient-ideal
membership is concluded here. Those require comparison of the chosen
weight finite `g'` with the weighted content coordinates. On blocks
without a predecessor, positive-weight cap boundaries vanish through
the lower induction object; negative-weight unit boundaries retain the
finite unit inverse and require their separate comparison. They must
not be set to zero by the principal-closure argument.
