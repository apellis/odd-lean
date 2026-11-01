# Ordinary unit and dot columns

DeformedMatrixComparison (4) compares the positive polynomial columns
with the adjunction unit followed by induction-dot powers. ELVUnitDotColumns
makes that comparison on the constructed maps, for every moving colour
and arbitrary old Hom endpoints.

inductionUnitDotSign(p,n) is sign(choose(n,2)•p). The theorem
inductionUnitDotSign_eq identifies it with sign(p)^choose(n,2), hence
(-1)^choose(n,2) for odd moving colour and 1 for even moving colour.
inductionDot_iterate_unit derives this scalar on actual balanced tensors,
retaining the whole coefficient, and adjunctionUnit_total_apply identifies
the packaged even adjunction unit with that tensor unit.

inductionUnitDotColumn is expressed in the canonical upperHomEquiv.
inductionUnitDotColumn_categorical identifies it literally with the total
of the existing adjunction unit followed by actualInductionDot powers.
inductionUnitDotColumn_apply identifies its value with the prescribed
scalar times canonicalAppendTarget(appendOutputEmbedding(single n b)).
There is no coefficient projection, chosen target equivalence or unit/dot
comparison premise.

Finally, unitDotPolynomialMap is the finite sum of these ordinary columns
with their prescribed scalar normalization. unitDotPolynomialMap_eq proves
equality of the complete linear map with canonicalAppendTarget composed
with appendOutputEmbedding.

The producer and concrete consumer pass scoped builds with warnings as
errors. The mixed-parity asymmetric datum and distinct endpoint orders
check the odd square sign, an even fifth power, the actual categorical
unit/dot expression for all powers and both moving colours, and the
whole polynomial map equality. All twenty-six owned declarations pass the
consumer audit. Full CI and the global audit remain integration gates.

The ordered-mate first-row identity and the construction of the full
parity-shifted module summand family remain separate. These are component
equalities for the ordinary unit and induction dot themselves.
