# Reservoir generators on the tensor-vacuum Hom

This attaches the reservoir generators to the initial input constructed in
[ELVWeightTensorVacuum](ELVWeightTensorVacuum.md), for
[SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §§2–6.

`TensorVacuumGenerators.dot` starts with the literal two-morphism
`selectedHom ◁ (elvRouquierData …).dot`, evaluated at the specified
`regularProbe`. Its `dotChart` applies reservoir E to the already proved
`selectedIso`, then uses the existing single-append comparison
`PowerWordWeightCross.appendIsoAtWeights`. Under this chart the map is
`PowerWordWeightDot.wordDotAt` on every original-weight component.

`TensorVacuumGenerators.cross` starts with the literal crossing whiskered
by the same Hom input and evaluated at that same probe. Its two
`pairChart`s apply the two chosen E functors to `selectedIso`, then use the
existing `recursivePairIso`. The crossing becomes precisely
`PowerWordWeightCross.wordFamilyCross`. The source word is `[j,i]` and the
target word `[i,j]`, matching diagrammatic composition and the established
reservoir reversal convention. Equal and distinct colours are included.

The proofs use supernatural naturality against the even `selectedIso`,
so no additional Koszul sign is introduced by this initial comparison.
The prescribed signed old-Hom dot and crossing operators are unchanged.
`dot_apply` and `cross_apply` give the identities on every vector of every
formal-content block. The actual intermediate original weights are
retained; no quotient of the weight group or root-map injectivity is used.

The paired consumer uses the connected asymmetric two-odd datum over `ℚ`
and the actual scalar-evaluated OLD probe tensor Hom. The independent
product of both odd coefficients supplies nonzero vectors in its one-E
and two-E values through these same charts. The literal whiskered dot,
equal odd crossing, and distinct odd crossing identities are applied to
those vectors. The all-vector forms are also instantiated.

These are the one-E dot and two-E crossing out of the specified vacuum
Hom. Generator transport in arbitrary longer word contexts and attachment
to a completed chosen OLD probe/reservoir record remain separate. No
literal swapped layer observation or nondegeneracy conclusion is asserted.
