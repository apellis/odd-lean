# Signed source composition in the actual word-module chart

Strict local producer and occupied paired-consumer checks pass. All 11 owned
declarations use only standard axioms. Full-library CI remains the integration
gate. This is the checked successor of the proposed b107e5ac snapshot.

This supplies the signed composition step required by
SwappedVacuumCoordinates, sections 4–5. `fromArrow_comp` proves whole-map
super-opposite composition for homogeneous old arrows: its factor is the
product of their total parities, including all exterior coefficients.
`fromArrow_smul` retains scalar multiplication.

`halfTurnOldHom_mem` proves that the existing full source half-turn followed
by the literal old quotient preserves this same total parity. `sourceMap`
is the corresponding linear map into morphisms of the unchanged regular
coefficient-power word modules at reversed words and twisted parameters.
`sourceMap_comp_homogeneous` matches the two signed composition factors.
`sourceMap_comp` extends ordinary source composition to arbitrary full source
arrows, including inhomogeneous inputs, by homogeneous decomposition.

`sourceMap_evaluate` identifies unit evaluation of this module map with the
previously checked `powerWordHalfTurnCoordinate`. The paired consumer uses
the asymmetric all-odd two-colour datum, its parameter twist, cutoff 20 and
power exponents 10. It checks both odd-colour orders, odd/even composition,
arbitrary arrows, explicit identity-plus-odd coefficient inputs, scalar
multiplication and coordinate evaluation. The two-exterior PBW vector
survives in the same two-strand target, and its `sourceMap` is proved nonzero
as a module morphism because its unit evaluation is nonzero.

This is a source-module chart with a proved composition law. It is not yet
identified with evaluation of the independently chosen weight action.
That requires scheduled coefficient annihilation and the actual old-to-
truncated, content and weight comparisons with the Rouquier generators.
The source-coordinate kernel is not asserted to be the chosen action-
evaluation kernel. Matrix/factor assembly and nondegeneracy remain separate.
