# Pulling the combined action back to the original weights

The explicit parameter choice in [SwappedVacuumParameters](SwappedVacuumParameters.md)
uses the pairing extension of [SwappedNondegeneracy §2](SwappedNondegeneracy.md#2-fix-the-observation-before-constructing-the-factors).
The final field consumer requires an action for the original datum.
This is the presentation pullback along `μ ↦ (μ,0)`.

Restricting the two Rouquier factors individually does not retain this
vacuum. Their occupied fibres have second weight coordinate `-P`, whereas
`ReservoirWeights.restrictRouquierFamily` samples `(x,0)`. All extended
roots have second coordinate zero. Translating either factor to the
occupied coset would change its individual local height by `-P`.
The extra heights cancel in the combined Hom action; therefore it is
that combined action which is pulled back.

`SKM.PairingExtensionDiagrams` defines `PairingExtension.inclusion` as a
`SigMap`. It retains each signed letter and generator shape, and embeds
every region. `inclusion_ob`, `inclusion_lay`, and `diagram_mkD` identify
the complete normal-form diagram. `relationLabel` and `linear_relation`
retain every defining relation of Brundan–Ellis Definition 1.5 and (2.6),
including both products of the augmented inverse and the finite
positive/negative windows. The unchanged heights and parities preserve
their scalars and signs.

`SKM.PairingExtensionPresentation` uses `SigMap.lift` to descend through
all contextual relations and superinterchange. Its `presentationFunctor`
is linear. `homMap` is the induced linear map at fixed original external
weight and unchanged signed boundary words; `homMap_id`, `homMap_comp`,
and `homMap_diag` give its exact action. No faithfulness premise or
nondegeneracy input is used.

`QuiverHecke.UpwardModuleAction.restrictPairingExtension` in
`PairingExtensionAction` pulls back an upward action at `(μ,0)` with the
same carriers at every word. This applies in particular to
`SupportedSectors.pointwiseUpwardModuleAction` with the explicit extended
highest weights and scheduled cutoffs.

The paired consumer constructs this supported model for connected mixed
colours, a repeated-colour source word, and an original weight with a
nonzero common-coroot-kernel coordinate. It constructs the original-datum
action, proves both actual probe vectors nonzero, and checks a nonzero
raw odd-dot image and both finite inverse windows. The original kernel
coordinate remains part of the target region.

The next attachment is compatibility with `alpha` and source-placed
`betaSYM`, followed by transport of the vacuum/corner observations.
Pullback of the action alone does not provide those comparison equations
or an observation for the field endpoint.
