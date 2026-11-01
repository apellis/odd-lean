# Weighted annihilation is preserved by old append induction

`oldQuotient_twist` retains the complete quotient-Hom parity twist.
`oldCoefficientBasis_slide` applies the proved full coefficient
supercommutativity calculation before passing through the old ideal;
`append_oldCoefficientBasis` is the literal old right-context map.

`induced_killsWeightedCoefficients` applies these identities to the actual
balanced induction along the existing old append superfunctor. Sliding the
coefficient across the tensor arrow, with its full parity twist, puts it
in the source image. Ordinary coend balance then applies its zero action
on the input module. This handles every high-weight coefficient monomial,
including odd generators, over any commutative ground ring.

`weightedInducedModule` consequently gives that same balanced tensor
module an action of the literal weighted-truncated category.

Producer and concrete consumers passed pinned direct Lean with warnings
as errors and both compatibility settings. All six owned declarations
passed the consumer axiom audit. The connected mixed-parity consumer
uses an even induction colour while retaining an odd coefficient
generator from another colour. Full CI remains the integration gate.

This is the reservoir-side induction prerequisite for
SwappedVacuumCoordinates §6, tracking #345. Comparison with induction
defined directly on the truncated category, and transport of its
adjunction and categorical inverse, remain separate. Binomial probe
specialization is not applied to the weighted quotient.
