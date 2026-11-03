# Quotient classes of actual regular-power word vectors

This constructs the inverse source-class map required by
[SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §§5–7. It uses
the exact kernel already established for
`powerWordHalfTurnCoordinate`: the transformed first-boundary ideal with
the unchanged literal elementary-power generators. No weighted ideal is
substituted for that power ideal.

`PowerWordQuotientCoordinates.surjective` proves that the full source
coordinate reaches every vector of the actual reversed regular-power
word module at the twisted parameters. This follows from the full
half-turn equivalence, the actual old quotient projection, and the
surjective balanced word generator. Combined with the proved exact
kernel, `quotientEquiv` is a linear equivalence

    full source Hom / transformed boundary-and-power ideal
        ≃ actual regular-power word vector space.

Its forward map is exactly `powerWordHalfTurnCoordinate` on each source
class (`quotientEquiv_mk`). The inverse linear map is `coordinate`, and
`coordinate_mk` recovers the literal source quotient class. These are
statements on every vector, over the ordinary commutative base ring; no
field or faithfulness hypothesis is introduced.

`sourceMap_apply_coordinate` proves the concrete chronological equality

    sourceMap(g)(powerWordHalfTurnCoordinate(b))
        = powerWordHalfTurnCoordinate(b ≫ g).

Here `sourceMap` is the existing actual signed old-Hom module map, not an
action defined by conjugating through `coordinate`. The equality uses its
already proved composition law: the signed half-turn and the signed
contravariant old-Hom operator have matching opposite-composition signs.
Both `b` and `g` may be inhomogeneous full-coefficient arrows.

Consequently `coordinate_action` gives the quotient-class square for an
arbitrary actual word vector: if its coordinate is the class of `y`, the
coordinate after `sourceMap(g)` is the class of `y ≫ g`. The input-class
equality is the usual premise of the desired corner square; no independent
generator comparison is assumed.

`halfTurnOldHom_coefficient` proves that the full coefficient endomorphism
is fixed by the half-turn and projected to its actual OLD coefficient
endomorphism. `sourceCoefficient_action` therefore identifies source
coefficient insertion with the literal `coefficientModuleAction` on the
regular-power word module. `coefficient_unit_class` sends that actual
coefficient action on the word unit to the unchanged source class.

Finally `affine_coefficient_class` applies the actual old-Hom affine map
after that actual coefficient action. Its coordinate is exactly the class
of `reservoirSourceOrder(sourceCoefficientHom a f)`, with arbitrary full
coefficient `a` and affine arrow `f`. Thus the source-order sign is retained
before bounded extraction; it is not removed by a coefficient involution.

The consumer supplies the connected asymmetric two-odd datum and a
connected mixed even/odd datum over `ℚ`. Bounded power injections prove
that the exterior inputs and their source quotient classes are nonzero.
It applies the chronological square to the literal old-Hom dot, tests the
actual coefficient action with `1 + δ`, and verifies the negative
source-order sign for an odd coefficient against an odd dot. The inverse
identities and surjectivity are also instantiated on arbitrary vectors.
Strict producer and consumer checks pass; all 18 owned declarations pass
the standard axiom allowlist.

## Remaining chosen-action attachment

The maps and vectors here are the actual regular-power OLD word maps.
The tensor-Hom entry and two-whisker comparisons are established in
[ELVTensorHomContexts](ELVTensorHomContexts.md). To connect them to this
source-class square, the contextual old append-dot and normalized crossing
arrows must be identified literally with
`halfTurnOldHom(sourceCoefficientHom 1 (diag layer))`, including reversal
of both outer words and the equal-colour crossing minus. The existing
contextual `halfTurn_dot` and `halfTurn_cross` generator tables provide the
affine presentation input to that equality.

After those endpoint and old-quotient transports, use the supported
`Gs`/`Ys`, the actual reservoir path-functor comparisons, and
[ReservoirLayerEntries](ReservoirLayerEntries.md) to attach the source-class
square to the literal layer matrix. The completed chosen OLD probe record
and `SwappedRelationData.upwardModuleAction_act_layer` are still required
for the relation-derived action. Likewise the actual source-placed bubble
coefficient action must be attached to `coefficientModuleAction` before
claiming `ev_vacuum` for that action. No `VacuumCornerEvaluation` or
nondegeneracy theorem is constructed here.
