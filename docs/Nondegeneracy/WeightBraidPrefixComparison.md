# The prescribed first weight crossing in the triple chart

For Brundan--Ellis (1.9), DeformedActionAssembly §6,
`ELVWeightBraidComparison.elvWeightBraidPrefix_comparison` proves that the
literal reassociated first weight crossing intertwines with the
normalized content prefix crossing through `elvWeightTripleComparison`.
It is an equality of whole module maps, valid for every input product
module at each supported triple block, in both moving parities.

The proof uses the selected first-pair chart factorization from
`WeightTriplePairComparison.md`. It inserts the already prescribed
pair-crossing component, applies the last induction, cancels the given
comparison isomorphisms, and uses the content inner-arrow comparison.
The equal-colour affine normalization remains in `contentCrossAffine`;
no new crossing or crossing-compatibility hypothesis is introduced.

The producer and paired regular-vacuum consumer pass scoped strict checks
and an all-owned axiom audit. This identifies the first of the two braid
operators through the selected chart. The second operator and the final
weight braid remain separate obligations.
