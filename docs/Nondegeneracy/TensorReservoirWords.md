# The selected tensor Hom along reservoir words

This supplies the selected whole-functor comparison needed between the
matrix word charts and the concrete tensor charts in
[SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §§2–6.

`ELVOld.TensorReservoirWords.pathHom` is the actual selected tensor-vacuum
Hom postcomposed by `ReservoirWord.word` of the unchanged chosen ELV
data. Its input is any upward labelled reservoir path from `(0,c)` to
`(0,0)`, including a path already reindexed along a crossing endpoint
equality. It retains the original weight `-ΛR + α(c)`.

`path_weight` proves that this weight is the original weight of the
reversed colour word. `pathHom_heq` compares the entire selected
postcomposition functor with `TensorVacuumWords.wordHom` of that reversed
word. `pathHomAt` applies only this proved endpoint weight transport, and
`pathHomAt_eq_wordHom` is equality of whole superfunctors. The proof uses
the actual `word_cons` and `wordHom_append` equations, with the prescribed
empty-word normalization. No replacement-object equality, factor-existence
premise, or equality only on a cyclic vector is assumed.

`valueChart` uses this equality followed by the existing chosen word
chart on the actual regular probe. `valueChart_hom_mem` proves it is even,
as required for odd factor-generator interchange. All original-weight
components and full coefficient carriers remain present.

These statements concern the specified selected tensor Hom and its
chosen E-word postcomposites. They do not assert a support or boundary
vanishing property for arbitrary objects of an unrestricted full Hom
category. In particular a weight collision does not identify the formal
content labels or remove other content blocks from that category.

The paired consumer uses connected mixed and two-odd data, the actual
ordinary OLD regular probe, actual selected tensor Hom, and two distinct
reservoir colours. It tests the whole-functor equality, its action on
arbitrary source morphisms, arbitrary paths with these boundaries, and
the empty path. The regular-probe chart has nonzero actual input vectors
obtained from full exterior-coefficient classes; their nonvanishing is
proved by bounded quotient injectivity and the inverse chart. Every path
and source datum is supplied concretely.

Strict producer and consumer checks pass; all 25 owned declarations pass
the standard axiom allowlist.

The remaining outer-word comparison identifies an actual reservoir word
ending at an arbitrary intermediate formal content with the prescribed
`PowerWordWeightContexts.contextFunctor` at its original weight. Together
with the pair associator this joins the generic surviving matrix word
charts to `TensorLayerClasses`' concrete all-vector quotient squares.
The intended supported Hom embedding and generator stability, relation
data, whole-module corner evaluation, and source-bubble/vacuum coefficient
field remain separate requirements; no complete `VacuumCornerEvaluation`
or faithful evaluation of all Hom transformations is claimed.
