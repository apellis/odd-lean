# Contextual layer operators in source quotient coordinates

This implements the single-layer square needed by
[SwappedVacuumCoordinates](SwappedVacuumCoordinates.md), §§5–7, before its
attachment to the swapped matrix representation.

`PowerWordLayerClasses.oldLayer` is the prescribed old append dot or
normalized crossing with both append contexts. Its source and target retain
the reversal of the original affine words. `oldLayer_eq` identifies this
operator with `halfTurnOldHom` of the original contextual layer with
coefficient one. In particular the equal-colour crossing retains its
half-turn sign; the physical crossing is not replaced by a coordinate-defined
action. `layerMap_eq` gives the resulting equality of whole regular-power
module maps, including all parity components and full coefficients.

For an arbitrary affine `Layer A`, `affineLayer` is the presentation image of
`Diagram.ofLayer A hA`, transporting only its unique region and word-object
boundaries. `affineLayer_eq` identifies that literal diagram with the
contextual generator diagram. `literalLayerMap` transports the physical
operator along the double-reversal word equalities, and
`literalLayerMap_eq` identifies it with the existing source map of that
literal affine layer.

`class_square` and `affine_class_square` prove the source quotient square for
every observation source word and every vector of the actual regular-power
word module. The only premise identifies the input vector's quotient class.
The output is the class of right composition with the coefficient-one
original layer. There is no independently supplied generator comparison and
no faithfulness premise for evaluation at the regular probe.

The paired consumer uses connected mixed and two-odd data, both nonempty
contexts, equal and distinct crossings, and nonzero exterior-coefficient
inputs. It also applies the literal affine-layer result to arbitrary vectors
and their input classes. Strict producer and consumer checks pass, and the
consumer audits all 25 owned declarations against the standard axiom
allowlist.

## Attachment to the swapped action

This is the quotient-coordinate component of `VacuumCornerEvaluation.ev_layer`,
not yet an evaluation of its complete swapped module. The remaining
attachment uses the original full coefficient products throughout:

1. At right sector `(0,0)`, take the tensor-vacuum `selectedHom`; at the
   left sector of the selected word, take the corresponding `wordHom`.
   Other supported-family entries must be specified, rather than inferred
   from evaluation at the regular probe.
2. Use `reservoirWordFunctorIso` to identify the surviving all-reservoir
   path functor, preserving the reversal of the source word.
3. Use the whole arbitrary-input Hom-entry squares of
   `TensorHomContexts` to identify the chosen dot or crossing entry after
   both contexts with the physical old operator used here.
4. `layerMap_reservoir_append` reduces the literal matrix sum at probe
   content zero to that entry, including its append transports. Combine
   this with `SwappedRelationData.upwardModuleAction_act_layer`, whose
   complete relation data are an explicit requirement, to obtain the
   literal action appearing in `ev_layer`.
5. Apply `affine_class_square` to its evaluated vector. Source-positioned
   bubble/coefficient action and the vacuum field remain separate from
   this coefficient-one layer calculation.

No complete intended OLD `ProbeReservoir`, supported-family evaluation, or
`VacuumCornerEvaluation` is asserted by this module.
