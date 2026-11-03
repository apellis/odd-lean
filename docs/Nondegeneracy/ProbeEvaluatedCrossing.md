# Equal crossings on the evaluated OLD probe

Brundan–Ellis Definition 1.5, (1.7), requires the same chosen negative
double-induction crossing on the probe factor. `ELVProbeEvaluatedCrossing`
restricts the literal OLD crossing to `ProbeEvaluatedModules`. This is a
full subcategory: the source and target already lie in the scalar-evaluated
category by induction closure, so the crossing retains its entire module
map, including its odd component.

The faithful full inclusion is the appropriate comparison boundary.
The reservoir family `ELVOld.elvRouquierFamily` in `ELVRouquierFamily.lean`
uses coefficient-power truncation; scalar probe values of χ need not be
nilpotent, so they do not generally define a specialization of that
truncated category. The scalar quotient `probeOldOrdinaryFunctor` in
`ELVProbeOrdinaryCategory.lean` is full, but is not asserted faithful on
OLD arrows, and therefore does not reflect their equations. Nor does the
ordinary global constructor provide a complete substitute:
`globalRouquierFamily` in `GlobalRouquierFamily.lean` takes
`GlobalLocalInversion`, while `globalRouquierFamily_multicolour` in
`GlobalRouquierMulticolour.lean` additionally takes `hBraid`, `hBraidEq`
and `hInvNe`. Restricting the existing OLD operators through the full
evaluated subcategory retains their literal equations without these
additional premises.

`probeEvaluatedEqualCrossComponent` is minus the existing physical
`gridDoubleCrossComponent`, with its existing balanced flattening.
`probeEvaluatedEqualCrossComponent_supernatural` retains the input-map law
in both parities. `probeEvaluatedEqualCrossComponent_naturality_twist`
also states the law on arbitrary sums of even and odd maps.
`probeEvaluatedEqualCross` is the resulting homogeneous transformation;
`probeEvaluatedEqualCross_native_total` identifies its underlying total
with the selected `inductionModuleCross`. The square-zero equation is
`probeEvaluatedEqualCross_square`, transferred from the literal OLD affine
relation through the faithful full inclusion.

The paired consumer uses connected even/odd data, actual regular probe
modules, their parity shifts and the odd parity isomorphism as input.
It checks both occupied content and empty content and audits every owned
declaration. The new producer and consumer are proposed until scoped
verification completes. Canonical stored-content transport, the other
crossing fields, and the augmented inverse lift remain separate obligations.
