# Pairing extension on joint PBW coordinates

`SwappedVacuumCoordinates.md` §7 transports an observation back from the
pairing extension without changing the original diagram or coefficient.
The affine category depends only on the unchanged Cartan entries,
parities and parameters. Its independently proved PBW basis (KKT
Corollary 3.15; BE §11) supplies a linear inverse of the exact presentation
map: `PairingExtension.affineEquiv_apply` identifies the basis equivalence
with `PairingExtension.presentationFunctor.map`, and
`presentationFunctor_nf` retains every normal-form index.

`sourceEquiv` tensors this map with the full coefficient algebra
equivalence. `coefficientHomEquiv` uses the identical polynomial/exterior
model of those coefficient algebras; `coefficientHomEquiv_source` proves
its square on every source-placed coefficient tensor. It is not a
replacement affine action. `coefficientHomEquiv_basis` retains the full
pair of coefficient and affine PBW indices; `extensionDegree_eq` retains
their joint degree. `coefficientHomEquiv_mem_atMost` and
`coefficientHomEquiv_mem_atLeast` preserve the two bounded-recovery
filtrations.

The paired consumer uses two connected odd colours, an independent
coroot-kernel summand in the weight group, two dotted strands, a
nonzero polynomial generator and both exterior generators. Their joint
basis vector has degree six and is nonzero before and after transport.
The exact affine presentation map also has a checked inverse round trip.
The producer and consumer pass strict scoped checks and an audit of
all nineteen owned declarations; full integration is separate.

## Proposed exact power-ideal continuation

Joint filtration transport alone does not identify an observation
kernel. The exact next target is

```
coefficientHomEquiv D Sc s t f ∈
  ker (powerWordHalfTurnCoordinate Dₑ Scₑ cutoff L s t)
↔ f ∈ ker (powerWordHalfTurnCoordinate D Sc cutoff L s t).
```

The proposed `PairingExtensionComposition` continuation upgrades the
existing affine presentation map to a superfunctor using
`LayerMap.lift_mem_homDeg`. Its box product with the identity of the
polynomial/exterior model should prove composition compatibility,
retaining the Koszul sign.

The proposed `PairingExtensionPowerIdeal` continuation retains three
literal generator families: `SYM.elvCoefficientIdeal`, each
`SYM.e i r ^ L (i,r)`, and `transformedCyclotomic` at the last strand.
The last family must retain both the monic odd/even coefficients and
`(-1)^(choose j 2)` half-turn correction. Composition compatibility and
surjectivity of `coefficientHomEquiv` then transport their two-sided span
in both directions. The existing `powerWordHalfTurnCoordinate_ker`
identifies that exact span with the actual kernel. These continuation
sources are proposed until independently checked and paired; they are
not premises of the proved PBW transport or a completed observation.

The composition draft has not passed: its affine parity instance elaborates,
but the bundled box-product target still needs explicit category parameters
and the tensor induction cases need alignment with the current API.
`PairingExtensionPowerIdeal` is untested and has no paired consumer.
No exact kernel transport is claimed.
