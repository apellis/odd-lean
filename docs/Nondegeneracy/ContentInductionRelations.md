# Content induction relation comparisons

The proposed `ELVContentWhiskeredMixedBraid.contentWhiskered_mixedBraid`
composes the independently whiskered pair crossings and uses the independent
single-letter dot correction. `ELVContentUncorrectedBraid.contentWhiskered_braid`
handles all remaining triples; `ELVContentDistinctSlides` supplies the two
distinct-colour slides on the same pair crossing and explicit common target
content. These sources and their concrete asymmetric odd consumers are drafts
until their build, consumers and axiom checks pass.

The corrected and uncorrected paths take their common intermediate contents and endpoint
equalities explicitly, retaining them as abstract variables through the source
comparison rather than expanding computed multiset transports. The concrete
consumers provide all these bookkeeping equalities. The prefix crossing is the
SVec Hom between evaluations of the actual triple induction functors. Its definition remains the existing independent
pair crossing, induced by the final letter and transported only through the
specified intermediate-content equality. This encoding retains the carrier
instances of the natural maps, avoiding repeated conversion through expanded
`ContentETripleSpace` abbreviations. It does not define a crossing by
conjugating a source operator. Both the corrected and uncorrected paths inline their literal prefix factors and compose
the existing normalization equalities by congruence of linear-map composition.
A single k-linear composition-congruence lemma fixes the ring and module
types before combining these equalities; no polymorphic semilinear composition
is inferred against expanded carrier terms. No separate equality that unfolds
a prefix alias is required by these proofs.
The comparison with the source-positioned map remains a separate proof; no
kernel or elaborator budget is increased.

The distinct-slide draft uses the positioned diagram slide relations directly;
it does not identify the singleton diagram dot by definitional equality with
the indexed dot. Pair comparison proofs use the forward commutative squares of the existing
induction comparison for inner/outer whiskering. Transport of a slide applies
the comparison's injectivity; it does not unfold a conjugation or inverse. Parity witnesses of both
source arrows are supplied explicitly after the two-transform tensor calculation.

Whole natural-transformation and weight-family relations additionally require
total-evaluation extensionality and compatibility with the actual successor
block functors. No local inverse, factor-action or nondegeneracy construction
is supplied by these component relation drafts.
