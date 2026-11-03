# Reindexed coordinates of the prescribed local inverse

For the local inversion relations in Brundan–Ellis (1.13)–(1.14),
`probeReindexLoopFunctor` transports whole super natural transformations
of the intermediate evaluated module category by inverse reindexing on the
input and reindexing on the output. It is additive, linear and parity
preserving. Reindexing the identity loop gives the identity strictly.

The chosen ordinary loop comparisons from `ProbeReindexLoops` lift to
`probeReindexLowerLoopSuperIso` and `probeReindexUpperLoopSuperIso`.
Their components remain even, and their total evaluations are exactly the
original ordinary components.

`probeReindexInvPos` and `probeReindexInvNeg` apply
`SuperSumInvTo.mapCoordinates` and `SuperSumInvFrom.mapCoordinates` to the
corresponding inverse records of `probeEvaluatedLoc`. The resulting five
finite inverse identities follow from functoriality and the even loop
isomorphisms. Each inverse entry is the reindexed original entry composed
with the specified loop comparisons. In particular, every row index is
retained, including indices outside the finite sum. There is no new choice
of inverse or coefficient-power quotient.

These declarations give inverses in the transported coordinates. Their
forward principal map and dotted rows are not yet identified here with
the selected stored-target mate and unit/counit rows. Those generator
compatibility squares are required before this construction gives the
stored-target local Rouquier record.

The consumer checks the total and off-diagonal finite identities for both
parities and both height directions, including reordered mixed-colour
contents. It also checks parity of inverse entries outside the finite
window and of the two whole loop comparisons.
