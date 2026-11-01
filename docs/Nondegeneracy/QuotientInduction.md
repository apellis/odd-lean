# The quotient-induction counit is an actual module isomorphism

The actual old-to-weighted-truncated functor is full: every quotient
arrow lifts to an old arrow. On balanced induction of a restricted module,
the existing counit evaluates a tensor by that arrow's action. Its inverse
is the existing unit at the old word with the same boundary.

`BalancedInduction.unit_counit_of_full` proves the second inverse product
for a full functor by lifting the tensor arrow and applying coend balance.
`quotientInductionCounitEquiv` specializes this to the literal quotient.
`quotientInductionCounitNatIso` proves naturality for the actual module
action. `quotientInductionCounitIso` is the resulting even module
isomorphism; its forward map is exactly the existing adjunction counit,
not a replacement comparison map. Both parity-zero components are the
existing counit and unit linear maps.

These results require neither coefficient flatness, finite dimension,
nor a field. Full exterior coefficients remain in the quotients.
They supply the quotient-induction step of SwappedVacuumCoordinates §6.

Producer and concrete consumers passed pinned direct Lean with warnings
as errors and both compatibility settings; all 30 owned declarations passed
the consumer axiom audit. The actual truncated representable tests both
inverse products, the counit on the mixed-arrow/identity tensor, and the
inverse on an odd-coefficient mixed-crossing vector proved nonzero at every
sufficiently large cutoff. Full CI remains the integration gate.

Next combine this counit with the proved induction-composition comparison
and preservation of weighted annihilation to identify old append induction
with the existing truncated append induction, retaining the adjunction.
This module alone does not transport the categorical matrix or construct
the full action or normalized vacuum identity.
