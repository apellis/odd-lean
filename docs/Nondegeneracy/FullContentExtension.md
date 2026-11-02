# Extension from a full content category

This supplies the content-module realization step in SwappedVacuumCoordinates §6.
The finite matrix multiplicities are constant on a fixed content block. Its
input modules therefore cannot silently be treated as arbitrary modules on
the entire old category.

For a full faithful additive linear superfunctor J : C → D, balanced induction
has an even unit isomorphism M ≅ Res_J Ind_J M. On a quotient tensor its inverse
is [h ⊗ m] ↦ M(J.preimage h)m. Linearity follows from full faithfulness;
balancing follows from preservation of composition by preimages. The two
inverse products use the identity preimage and the balancing relation.
The forward map is exactly the established adjunction unit, so the comparison
is natural against every supernatural module map, including odd ones.

The declarations are `BalancedInduction.fullyFaithfulUnitInverse`,
`fullyFaithfulUnitNatIso`, `fullyFaithfulUnitIso`,
`fullyFaithfulUnitIso_hom`, `fullyFaithfulUnitNaturalIso`, and the literal
old-content specialization `oldContentExtensionUnitIso`, in
`ELVFullyFaithfulInduction.lean`.

No coefficient flatness, finite dimension, categorical cocompleteness or
equivalence with arbitrary D-modules is assumed. The append/inclusion square
is already literal; its chosen induced-module comparison is a further
obligation before this bridge can be used in the arbitrary-module matrix
inverse.

The producer and paired concrete consumer pass strict source checks, and all
24 owned declarations pass the axiom audit. The consumer uses the actual
full-coefficient old content inclusion on two distinct mixed-parity words
and proves a mixed crossing with a nonzero exterior coefficient, and its
image under the unit, survive every sufficiently large cutoff. Full
exact-head CI remains required before integration.
