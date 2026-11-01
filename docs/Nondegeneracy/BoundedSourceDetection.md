# The bounded recovery source survives the reservoir quotients

`finite_nf_dotLength_le` proves that bounded dot count gives a finite
normal-form set for a fixed boundary pair, without finite colours.
`exists_nf_degree_upper_bound` bounds its integer degrees.
For finite colours, the established coefficient-degree/weight estimate
then proves `exists_extendedAtMost_le_jointPBWWindow`: the exact
`ExtendedAtMost` source window of bounded recovery fits into a single
cutoff-independent joint coefficient/PBW window.

`extendedAtMost_detected_at_high_cutoffs` proves injectivity of the
literal composite coefficient quotient and weighted-truncated cyclotomic
quotient on that recovery window, for every sufficiently large cutoff.
It includes empty Hom corners without a supplied permutation witness.
`truncated_quotients_jointly_detect` separates every full source Hom by
these actual quotients. The coefficient and cutoff bounds retain arbitrary
polynomial and exterior products and are chosen in the required order.

Producer and closed consumers passed pinned direct Lean with warnings as
errors and both compatibility settings; all eight owned declarations passed
the consumer axiom audit. Consumers include survival of a nonzero odd
exterior coefficient times a mixed crossing, vacuum, unequal strand counts,
and the jointly-detecting statement. Full build with warnings as errors, global axiom audit and concrete consumers passed before research integration.

This supplies the bounded source comparison in SwappedVacuumCoordinates §6
and tracking #345. The intermediate statements work over a commutative
ring with homogeneous parameters and a positive symmetrizer. Their
finite-colour scope fits the established finite-colour nondegeneracy
reduction; no arbitrary-ring nondegeneracy conclusion is claimed.
The categorical action, its descent and its normalized vacuum-coordinate
identity are still required to invoke recovery.
