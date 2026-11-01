# Naturality of weighted append induction

The comparison required by
[SwappedVacuumCoordinates §6](SwappedVacuumCoordinates.md) must be natural
in its input module. The pointwise isomorphism from
[AppendQuotientComparison](AppendQuotientComparison.md) alone did not supply
this assertion.

`quotientInducedWeightedModuleIso_naturality` proves naturality of the
canonical quotient-induction/descent isomorphism for every supermodule
map between annihilated old modules. The identity-on-vectors restriction
comparison and the existing adjunction counit supply the commuting square;
no evenness condition is imposed on the input map.

`weightedFunctorDescent` descends a functor whose objects kill the literal
weighted coefficient ideal. `weightedAppendFunctor` specializes it to old
append induction after restriction. `appendWeightedNaturalIso` composes the
quotient comparison, the two existing induction-composition isomorphisms,
the literal append/quotient square and the quotient-induction counit.
Its components equal the already constructed `appendWeightedModuleIso`,
as proved by `appendWeightedNaturalIso_app`.
Finally `appendWeightedModuleIso_naturality` gives the naturality square
directly for those existing pointwise components.

All maps are actual supermodule morphisms. Naturality includes arbitrary
sums of even and odd maps and retains every coefficient, including the
odd weighted generators. Chosen dot/crossing/adjunction intertwining and
content/weight assembly are separate obligations.

The strict producer and concrete consumer pass, with all 31 owned-declaration
axiom checks. The consumer uses an actual truncated representable and its
canonical odd parity isomorphism, tests the naturality square and both inverse
products, and retains a mixed-crossing vector with an odd coefficient that
is proved nonzero at all sufficiently large cutoffs. Full CI remains required
before integration; see [STATUS](STATUS.md).
