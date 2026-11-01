# Modules descend through the weighted coefficient quotient

This is the reservoir-side quotient transport in SwappedVacuumCoordinates
§6. `KillsWeightedCoefficients` asks that an existing old-category
supermodule kill every coefficient monomial of weight at least N at every
word, including odd generators. `oldModuleRawMap_kills_truncatedIdeal`
proves annihilation of the complete literal defining ideal from those
generators and the already imposed old ideal.

`weightedModule` is a supermodule on the actual `TruncatedCategory`.
Its vector spaces and prescribed arrow maps are retained, via the proved
quotient lift. `oldTruncateFunctor`, `weightedRestriction` and
`weightedRestriction_kills` pull actual truncated modules back to this
annihilator class; `weightedModule_restriction_map` proves the map roundtrip.

`weightedModuleHom` descends every natural module map componentwise,
preserving both parities, identities and composition. `weightedModuleIso`
therefore preserves the chosen maps and both inverse products of an existing
module isomorphism. No flatness, finiteness or parity restriction on the
annihilated coefficient generators is imposed.

Producer and concrete consumers pass pinned direct Lean with warnings as
errors and both compatibility settings; all 36 owned declarations pass the
consumer axiom audit. The consumer constructs actual truncated covariant
representables on connected odd data, pulls them back, and descends a
nonidentity negation isomorphism. Its action is tested on an odd-coefficient
mixed-crossing vector proved nonzero at every sufficiently large cutoff.
Full CI remains the integration gate.

This does not prove that old induction preserves the annihilator class,
nor compare old and truncated balanced induction or its adjunction.
Those are required before transporting the full categorical inverse.
Binomial probe specialization belongs to the untruncated old category:
the present construction does not evaluate the weighted reservoir quotient
at nonnilpotent scalar coefficients. No full action or nondegeneracy is claimed.
