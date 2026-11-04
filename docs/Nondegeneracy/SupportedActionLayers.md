# Presented layers in the supported action

SwappedVacuumCoordinates §§5–7 needs the literal native layer
calculation on the module action used by bounded recovery.
`pointwiseUpwardModuleAction_act_layer` in
`SwappedAssembly/SupportedActionLayers.lean` supplies this attachment.

For a valid layer whose boundaries are the specified upward words, the
complete action of its presented diagram is

```
interpretation.res cod ∘ interpretation.op layer ∘ interpretation.ext dom.
```

The module-action constructor uses the functor lifted from the actual
supported local interpretation. `Presentation.lift_diag` identifies
its value on the presented diagram with the original diagram functor;
`LocalInterpretation.functor_map_layer_hom` computes that diagram as
the literal local layer operator. The presentation obligations are
supplied by `pointwiseObligations`, so the theorem has no separate
relation, inverse, permutation or comparison premise.

Together with `tensorOriginalWordEntry_layer`, this gives the action
side of the affine layer observation used by
`UpwardModuleAction.toSwappedVacuumEvaluation`. The original-Hom
charts, regular-probe evaluation and quotient normalization retain
their separate prescribed maps.

The paired consumer uses the two-odd collision datum, the same tensor
source and vacuum target as the complete action, and its proved
nonzero matrix vacuum. It constructs the actual odd dot layer and
applies the linear-map formula both as a map and at that vacuum.
Owner-module and nonzero-vector audits use the standard axiom
allowlist.
