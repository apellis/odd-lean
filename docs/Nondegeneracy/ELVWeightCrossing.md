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
compatibilities, remain necessary for the full factor action. The source is
under local verification; no full-CI claim is made here.

## Independent pair comparison

`ELVWeightCrossingComparison` addresses the first endpoint comparison.
`contentPairInductionTo_eq` substitutes an abstract intermediate content
before specializing to a block successor. The equations
`contentPairComparisonTo_hom` and `contentPairComparisonTo_inv` show that this
substitution commutes with the existing direct-word comparison. Thus the
canonical pair comparison introduces no second associativity choice.

`elvBlockPairCanonical_eq` applies this construction to the actual block
pair, and `elvEFunctor_comp₂_contentPair_eq` includes evaluation at the source
weight block. `elvWeightCross_contentPair` identifies the assembled weight
crossing with the independently normalized `contentEPairCrossTransform`,
retaining both endpoint equality maps. The scope is an equality of whole
module morphisms for arbitrary input modules, rather than an equality only
on chosen balanced generators. Triple whiskering and relation transport
remain subsequent obligations. This comparison source is also under local
verification.
