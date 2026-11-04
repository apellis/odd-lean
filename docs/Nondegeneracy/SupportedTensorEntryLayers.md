# Layers on the original tensor row

SwappedVacuumCoordinates §§5–7 attaches the literal supported matrix
action to the whole original tensor Hom before evaluating its source
unit or taking quotient coordinates.

`tensorOriginalWordEntry_layer` in
`SwappedAssembly/SupportedTensorEntryLayers.lean` proves that observing
the native one-layer action is chronological postcomposition by
`tensorOriginalWordLayer`. Both actual source and target paths, the
original external weight, and the full source Hom are retained. The
generator family may be the complete `swappedGens` of the supported
action. No layer comparison hypothesis is assumed.

For the canonical input-weight equivalence `E`, global source and
target isomorphisms `e` and `d`, and actual matrix entry `m`, the
original layer is

```
E.functor.preimage (e.inv ≫ m ≫ d.hom).
```

The theorem follows from the proved matrix-row postcomposition law
`tensorVacuumRowProjection_layer` and
`TensorEntryPullback.map_square`. `TensorEntryPullback.arrow_square`
supplies the required square for this prescribed arrow. Thus there is
no separately supplied generator square.

`tensorOriginalLayerChart` changes the global target to a specified
local whole-Hom chart. Its isomorphism is the functor preimage of
`global.symm ≪≫ local`. `TensorEntryPullback.arrow_chartChange` gives
the resulting canonical conjugacy. The dot and crossing
specializations belong to `SupportedTensorEntryLayerCharts`.
Compatibility of these whole-Hom changes with the global and local
charts after evaluation at the regular probe is a separate input to
the final affine quotient observation. A heterogeneous equality of
value charts alone is not asserted to prove that compatibility.

The paired consumer uses the two-odd collision datum and the proved
nonzero tensor matrix vacuum. It instantiates the actual complete
action's odd dot layer on that same matrix, with the layer, endpoint,
paths and upward certificates all constructed. The full action module
remains nonzero. Owner-module and constructed-vector audits retain
only the standard axioms.
