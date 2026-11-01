# Content induction relation comparisons

The proposed `ELVContentWhiskeredMixedBraid.contentWhiskered_mixedBraid`
composes the independently whiskered pair crossings and uses the independent
single-letter dot correction. `ELVContentUncorrectedBraid.contentWhiskered_braid`
handles all remaining triples; `ELVContentDistinctSlides` supplies the two
distinct-colour slides on the same pair crossing and explicit common target
content. These sources and their concrete asymmetric odd consumers are drafts
until their build, consumers and axiom checks pass.

The prefix crossing has the SVec Hom type between evaluations of the actual
triple induction functors. Its definition remains the existing independent
pair crossing, induced by the final letter and transported only through the
specified intermediate-content equality. This encoding retains the carrier
instances of the natural maps, avoiding repeated conversion through expanded
`ContentETripleSpace` abbreviations. It does not define a crossing by
conjugating a source operator. The comparison with the source-positioned map
is a separate proof; no kernel or elaborator budget is increased.

Whole natural-transformation and weight-family relations additionally require
total-evaluation extensionality and compatibility with the actual successor
block functors. No local inverse, factor-action or nondegeneracy construction
is supplied by these component relation drafts.
