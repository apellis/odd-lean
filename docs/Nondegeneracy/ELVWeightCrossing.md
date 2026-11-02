# Full-coefficient weight crossing

This develops the weight-assembly obligation in
[DeformedActionAssembly](DeformedActionAssembly.md) §6, using the actual
full-ELV product categories and the two-successor comparison from
[ELVWeightPairInduction](ELVWeightPairInduction.md).

For a target block in the image of the double successor, the source block is
unique. `elvWeightPairComparison` identifies the corresponding coordinate of
the composed product induction with evaluation at that source block followed
by direct two-letter content induction. Its intermediate block is the actual
first successor. Both directions of the comparison are even.

`elvWeightCrossVia` transports the prescribed content crossing through the
two comparisons. Its component identity and comparison square are
`elvWeightCrossVia_component` and `elvWeightCrossVia_comparison`. The affine
representative is `contentCrossAffine`: distinct colours use the raw crossing,
whereas equal colours retain the existing negative normalization. No scalar
is selected afresh during weight assembly.

`elvWeightCross` assembles these components on the existing product induction
functors. At blocks without a double predecessor the source coordinate is
zero, including when the outer predecessor exists and the inner one does
not. Its naturality includes the Koszul sign for odd input-module maps, and
`elvActionCross_mem` identifies the parity as the product of the two colour
parities. Neither finite colours nor finite weight fibres are assumed.

This construction does not yet transfer the independent pair/triple
whiskerings or their polynomial relations to the weight functors. Those
comparisons, followed by the categorical inverse and adjunction
compatibilities, remain necessary for the full factor action. The crossing
producer and its mixed-colour consumer pass strict scoped Lean checks;
the consumer retains equal-colour crossings, the absent inner predecessor,
and naturality on the canonical odd isomorphism of the vacuum family.
All 28 owned declarations pass its axiom audit. Full CI remains separate.

## Independent pair comparison

`ELVWeightCrossingComparison` addresses the first endpoint comparison.
`contentPairInductionTo_eq` substitutes an abstract intermediate content
before specializing to a block successor. The equations
`contentPairComparisonTo_hom` and `contentPairComparisonTo_inv` show that this
substitution commutes with the existing direct-word comparison. Thus the
canonical pair comparison introduces no second associativity choice.

`elvBlockPairCanonical_eq` applies this construction to the actual block
pair, and `elvEFunctor_comp₂_contentPair_eq` includes evaluation at the source
weight block. `elvWeightPairComparison_eq` proves coherence as an equality of
whole natural isomorphisms: the existing direct-word comparison is the
literal endpoint equality followed by the independent canonical content
pair comparison. This retains both directions without expanding the large
product-induction component casts. The direct affine crossing formula is
already supplied by `elvWeightCrossVia_component`; triple whiskering and
relation transport remain subsequent obligations. The comparison producer
and its asymmetric vacuum consumer pass strict scoped Lean checks, including
the twisted parameter category and both comparison directions. Its consumer
audits all ten owned declarations. Full CI remains the integration gate.
