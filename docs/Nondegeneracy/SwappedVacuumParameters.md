# Explicit parameter choice for bounded swapped observations

This is the parameter join in [SwappedNondegeneracy §2](SwappedNondegeneracy.md#2-fix-the-observation-before-constructing-the-factors)
and [SwappedVacuumCoordinates §§6–7](SwappedVacuumCoordinates.md#6-transfer-of-detection-by-the-actual-ideal-bound).
It does not assert the remaining vacuum or normalized bubble comparison.

For a fixed external weight `μ`, source word `s`, and coefficient/PBW bound
`d`, retain the existing schedule

```
N₀ = d + 2 * choose(length(s), 2) + 1
Pᵢ = 2*N₀ + 2*max(hᵢ(μ), 0)
Nᵢ = 2*N₀ + |hᵢ(μ)|.
```

The declarations in `OddMath.QuiverHecke.SwappedVacuumParameters` use the
existing `probeExponent`, `probeLevel` and `reservoirLevel`, rather than
introducing a second schedule. `probeWeight` and `reservoirWeight` are
the explicit weights `(0,P)` and `(-μ,P)` in `ReservoirWeights.pairingExtension D`.
`weight_difference` proves their literal difference is `(μ,0)`; it does
not identify weights having the same coroot values. `probeCutoff_eq`
identifies the actual factor cutoff with `P`, including the different
odd and even probe exponents. `probe_pairing` and `reservoir_pairing`
are precisely the highest-weight equations required by `elvProbeReservoir`.
`probeExponent_pos` and `cutoff_bounds` give positivity and the common
strict lower observation bound.

Choose every elementary coefficient-power exponent to be `N₀`.
`coefficientPower_pos` proves positivity and `coefficientPower_weight`
proves `N₀ ≤ L(j)*elementaryWeight(j)`. This supplies the only power
inequality in `powerWordHalfTurnCoordinate_kernel_le_vacuumWindow` and
`powerWordHalfTurnCoordinate_reservoir_injective`.
The upper coefficient bound is already constructed, separately:
`ELVOld.PowerWordContent.powerBound D cutoff L` is
`SYM.elvPowerWeightBound D cutoff L + 1`, and `word_killsWeighted`
puts every scheduled regular-power word module in that same coefficient
truncation. `SupportedTensorFamilies.tensorSourceFamily` and
`tensorTargetFamily` use this exact bound. Support and finite-series
bounds may consequently be chosen afterwards.

The paired consumer uses connected even/odd colours, a repeated-colour
word, positive and negative coroot values, and a nonzero original
coordinate in the common coroot kernel. It also applies the constructed
constant powers to the actual half-turn coordinate injectivity theorem.

The final field endpoint can be filled directly by
`UpwardModuleAction.toSwappedVacuumEvaluation`, using the action from
`SupportedSectors.pointwiseUpwardModuleAction`. The required inputs are
the raw coefficient action and vacuum, the weight-preserving bubble
substitution and its source-placed identity, the actual corner quotient
with its ideal bound, and the all-affine coordinate identity. The generic
linear splitting and recovery are already in
`SwappedVacuumEvaluation.windowSplitting`, `recover_coordinates`, and
`toBoundedCyclicRecovery`. There is no need to construct the stronger
global `SwappedRelationData` field of `SwappedVacuumObservation` merely
to use the final endpoint.

For arbitrary colours, the existing consumer is
`nondegeneracy_of_restrictColours_vacuum_evaluations`. It combines finite
witnesses, `upward_independence_of_coefficientMap`, and
`SKM.nondegeneracy_of_upward_independence`. Over characteristic-zero
fields this supplies `SKM.CharZeroFieldNondegeneracy D`; the existing
`SKM.nondegeneracyConjecture_of_charZeroField` then gives the stated
homogeneous-parameter ground-ring theorem with `2` invertible.

One distinct attachment remains between the extension-weight model and
these original-weight endpoints. Its desired type is

```
A : UpwardModuleAction (pairingExtension D)
      (pairingExtensionScalars D Sc) (μ,0)
⊢ UpwardModuleAction D Sc μ
```

The carriers should remain `A.V t`, with the action pulled back along
the SKM diagram map induced by `x ↦ (x,0)`. This needs the induced
linear map on presented Homs and its compatibility with `alpha`,
source placement, and `betaSYM` for the supplied units. The currently
available `restrictRouquierFamily` and `restrictRouquierMulticolour`
only restrict factor data. `pairingExtensionCScalars`,
`pairingExtensionSymmetrizer`, `pairingExtensionScalars_homogeneous`,
and `pairingExtensionScalars_parameterTwist` already provide the
parameter and normalization transports. The `SigMap` and relation
transport in `SKM.FiniteColourRestriction` give a reusable pattern for
the missing presentation map; no faithfulness of the embedding is
required for pulling back an action.
