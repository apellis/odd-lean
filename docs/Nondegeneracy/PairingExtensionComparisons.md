# Affine and normalized coefficient comparisons for the pairing extension

This supplies the `alpha` and `betaSYM` squares needed after
[pulling back the combined action](PairingExtensionAction.md), as in
[SwappedVacuumCoordinates §7](SwappedVacuumCoordinates.md#7-concrete-bounded-recovery-with-the-original-source-indices).

`SKM.PairingExtensionBubbles` proves `homMap_etaP`, `homMap_epsP`,
`homMap_bubL`, `homMap_bubR`, and `homMap_oddBubble`, retaining every
height case, the supplied units, and their parity signs.
`homMap_bubAt_betaSYM` identifies the complete source-placed normalized
coefficient algebra, including arbitrary ordered products of odd
coefficients. It is not an assumption about the chosen module action.

The coefficient algebra transport `coefficientEquiv` is the composite
of the original polynomial/exterior equivalence with the inverse
equivalence for the extended datum. Their polynomial/exterior targets
are the same. `coefficientEquiv_ι` proves that each elementary and odd
generator is retained. This explicit equivalence is necessary because
the abstract coefficient presentation is indexed by the datum; it is
not a definitional equality of the two quotient types.

`QuiverHecke.PairingExtensionAffine` defines the affine
`PairingExtension.presentationFunctor`. It keeps each raw diagram,
including all equal-colour and distinct-colour crossings. All affine
relations and superinterchange descend. `alpha_map` proves the square
for every affine morphism: original upward labelling followed by the
SKM presentation map equals extended upward labelling after this affine
functor. It is not limited to a chosen normal form or a bounded window.

The paired consumer has two connected odd colours and an original
weight with a nonzero common-coroot-kernel coordinate. The supplied
normalization is `-1` at that coordinate and `1` at coordinate zero.
It checks the full source-placed image of a nonzero two-odd exterior
basis coefficient, the positive and negative normalized bend cases,
and the exact affine crossing square. The producers and consumer pass
strict checks, with all 27 bubble and 46 affine declarations audited.

These comparisons do not themselves identify the power-quotient corner
kernel. The next transport uses the independently proved affine PBW
basis to invert the exact affine functor, identifies its tensor with
`coefficientEquiv` through `sourceTensorEquiv`, and retains the joint
coefficient/PBW degree. Transport of the actual coefficient-power and
cyclotomic ideal generators is required before transferring the final
vacuum/corner observation to the original datum.
