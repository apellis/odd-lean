# Signed reversal in actual old cyclotomic Homs

`HalfTurn/OldQuotient.lean` attaches the full affine half-turn to the actual
old category used by the reservoir modules, as required by
`SwappedVacuumCoordinates.md` §§5–6.

`halfTurnOldHom` sends a full source coefficient/affine Hom from `s` to `t`
to the existing `OldCategory` Hom from `reverse t` to `reverse s`, at the
parameters `parameterTwist D Sc`. It is the proved `htCoef` followed by the
actual coefficient quotient and the literal old first-boundary quotient.
Its target is not a replacement quotient.

`halfTurnOldHom_ker` identifies its kernel exactly with the transformed
last-boundary ideal with no extra coefficient generators. The comparison
uses `sourceToOldHom_ker` from the exact actual/source presentation theorem,
then the earlier contextual half-turn ideal identification. No vacuum
kernel or action-faithfulness assertion is assumed.

`halfTurnOldHom_comp` is the signed chronological composition formula in
the actual old target Homs. Its sign is the product of the two total
coefficient-plus-affine parities, so includes all exterior coefficients.

`halfTurnOldHom_injective_on_extendedAtMost` and
`halfTurnOldHom_reservoir_injective` give bounded source detection in those
literal old Homs. They retain the explicit inequality
`d + 2 * choose(length(s), 2) < N` and the prescribed `reservoirLevel`
schedule, respectively.

For literal elementary powers, `halfTurn_oldElementaryPowers_preimage`
proves that the preimage of the actual old ideal plus its actual scalar
power span is exactly `TransformedIdeal` with the same source powers.
The source powers are automatically even, their exponents are unchanged,
and no weighted/power ideal equality is used. This statement compares
submodules of the existing full ELV Homs; it introduces no quotient category.

The paired consumer uses asymmetric odd parameters, checks the actual
reversed old category endpoints and signed composition, and instantiates
the prescribed reservoir schedule and literal-power preimage. A joint PBW
basis vector with one odd coefficient is proved nonzero in the actual old
Hom after reversal at a concrete cutoff.

Verification: strict pinned producer and paired consumer checks passed.
The consumer audits all 11 producer-owned declarations, including private
and generated declarations, against the repository's allowed axioms.

The remaining evaluation step must show that these coordinates are the
ones induced by the chosen reservoir/vacuum action and normalized bubbles.
The results here do not assert that evaluation identity or nondegeneracy.
