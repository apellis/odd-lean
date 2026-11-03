# Bounded detection in the reversed first-boundary quotient

`HalfTurn/BoundedDetection.lean` attaches the proved half-turn quotient
comparison to the coefficient/PBW separation bound in
`SwappedVacuumCoordinates.md` §§5–6. It uses the actual linear map

`halfTurnBoundaryClass x = [htCoef x]`

whose target is the first-boundary quotient for `parameterTwist D Sc` on
reversed words, with any specified coefficient generators also imposed.

`halfTurnBoundaryClass_ker` proves that its kernel is exactly the transformed
last-boundary ideal `TransformedIdeal`. This equality uses the earlier
contextual ideal identification; it is not an extra evaluation hypothesis.

`halfTurnBoundaryClass_injective_on_extendedAtMost` combines that comparison
with the existing transformed-ideal weight bound. If all strand cutoffs and
all specified coefficient generators have weight at least `N`, then the
map is injective on the joint coefficient/PBW window of degree `d` whenever

`d + 2 * choose(length(s), 2) < N`.

`halfTurnBoundaryClass_reservoir_injective` instantiates this for the literal
reservoir schedule `reservoirLevel D μ s d`, with its prescribed
`vacuumCutoff s d`. The full exterior coefficient algebra is retained.
The only assumptions about additional coefficient generators are their
proved homogeneous parity and their actual coefficient-weight lower bound.

The paired consumer uses the asymmetric two-odd-colour datum with Cartan
entries −2 and −4. At a two-strand word and window degree one, it imposes
the even coefficient `e_false,1` of weight four and the odd coefficient
`delta_true * e_false,1` of weight five. It proves both weight bounds and
parities, instantiates arbitrary-cutoff and reservoir-schedule detection,
and proves that an occupied odd coefficient/PBW basis vector remains
nonzero in the actual target quotient.

Verification: strict pinned source and paired consumer checks passed.
The consumer audits all seven declarations owned by the producer, including
private/generated declarations, against the repository's allowed axioms.

This supplies the bounded affine quotient coordinate input. Identifying
that coordinate map with evaluation of the chosen reservoir/vacuum action
and its normalized bubble coefficients remains separate work.
