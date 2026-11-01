# Parity of the prescribed mixed coefficients

The unit of an endomorphism ring determines its existing categorical
isomorphism through `Aut.unitsEndEquivAut`. The supercategory inverse-parity
lemma therefore preserves the parity of a homogeneous unit inverse.

On the literal target-J summand, both the probe-pre dot and chosen reservoir-
post dot retain the moving colour's parity under whiskering and Hom parity
shift. For odd colour, their square difference is even, so its inverse is even
and the numerator-first coefficient is odd. For even colour, the target
linear difference and its inverse are even.

The coefficients are exactly `elvMixedOddCoefficient` and
`elvMixedEvenCoefficient`; no coefficient is replaced or renormalized. Their
respective existing Π-Hom witnesses are reused in separate sections, preserving
the constructors' literal module and shift data.

Both coefficient-parity statements and concrete odd/even existing ordinary-
probe/full-ELV consumers pass strict local checks with warnings as errors. The
consumer audits all 5 owned declarations, including private/generated ones,
against propext, Classical.choice, and Quot.sound. Full CI is the integration
gate.
