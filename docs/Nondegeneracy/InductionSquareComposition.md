# Two-letter coend square comparison

This is proposed source for the chosen crossing transport in
[DeformedActionAssembly](DeformedActionAssembly.md), sections 5–6.
The producer and paired-consumer gates have not passed; no completed
comparison is claimed here.

Two squares `J ⋙ Q = Q ⋙ T` and `K ⋙ Q = Q ⋙ S` give
`(J ⋙ K) ⋙ Q = Q ⋙ (T ⋙ S)`. The proposed
`coendSquare_comp_endpoint` identifies its inverse endpoint map with
`S` applied to the first inverse endpoint map, followed by the second
inverse endpoint map. Naturality of the second square gives
`coendSquare_comp_coefficient`, retaining the intermediate coefficient
order rather than silently commuting the two arrows.

For an inner module map `f : L → Q* N`,
`coendSquarePairLinear` applies its even component inside outer induction,
then the canonical outer `coendSquareMap`. Keeping `L` and `N` abstract
makes the coefficient and vector maps independent of a nested induced
superspace presentation. The proposed `coendSquarePairLinear_flatten`
says that the selected inner generator formula forces compatibility with
the old and truncated canonical induction flattenings. On nested tensor
generators both sides reduce to `coendSquare_comp_coefficient`.

The remaining formal step is to express the specialized inner component
and flattening through typed maps on literal coends. A nested induced
module carrier should be normalized before it is specialized; its
identification must not be assumed from a failed conversion. The selected
weighted comparison and crossing application still need their own
literal generator formulas and concrete consumers.
