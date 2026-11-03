# Actual reservoir words as the chosen E contexts

This supplies the outer-word functor comparison needed in
[SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §§2–6, after
[TensorReservoirWords](TensorReservoirWords.md).

`ELVOld.ReservoirContexts.word_weight` proves the original-weight endpoint
of any upward reservoir path from `(0,c)` to `(0,d)`. The terminal formal
content `d` may be nonzero. The endpoint is the successive context weight
starting at `-Λ + α(d)` and reading the reversed labelled colour word.
Neither the original weight group nor the formal content labels are
replaced.

`word_heq` identifies the entire actual `ReservoirWord.word` of the
unchanged `elvRouquierData` with the chosen `TensorHomContexts.context`
superfunctor. The proof compares the prescribed E functors recursively,
using the append equation for context composition and the actual
reservoir edge weights. `wordAt` applies only the proved endpoint weight
transport, and `wordAt_eq_context` is equality of the resulting whole
superfunctors. Every source object, morphism, coefficient and parity
component is retained. No generator comparison or replacement-object
equality is assumed.

The equality holds for the ambient original-weight products. It does
not assert exact-content support or boundary vanishing for arbitrary
objects of those products, nor for arbitrary objects of an unrestricted
Hom category. Applying the same actual E functors to a collision block
does not identify that block with the formal content labeling the path.
The intended supported Hom construction must still supply its own exact
source and target contents and generator stability.

The paired consumer uses connected mixed and two-odd data, the actual
chosen ELV E functors, nonzero terminal formal content
`d = single false 1`, and a two-colour outer reservoir path. Its actual
input is the full regular-power one-letter family at its proved original
weight. The output is compared with the prescribed three-letter context
chart. Nonzero actual output vectors arise from full exterior-coefficient
classes, with nonvanishing proved by bounded quotient injectivity and the
inverse chart. The whole-functor comparison is also applied to arbitrary
ambient source morphisms. All content and original-weight equalities
needed by these examples are proved.

Strict producer and consumer checks pass; all 18 owned declarations pass
the standard axiom allowlist.

For the observation attachment, `TensorReservoirWords` identifies the
actual selected tensor Hom followed by its right reservoir word with the
chosen append-word Hom. The present equality identifies the actual left
reservoir word with the prescribed outer context. The remaining pair
associator and endpoint transports must be retained when transporting the
literal dot/crossing cell between these two functor comparisons.
`TensorLayerClasses` then supplies the concrete all-vector source quotient
square. The exact-content Hom embedding and stability, relation-derived
whole-module action, and source-bubble/vacuum coefficient field remain
separate requirements; no complete `VacuumCornerEvaluation` or faithful
evaluation of all Hom transformations is asserted here.
