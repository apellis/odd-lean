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

`probeEvaluatedEqualCrossComponent` is the active homogeneous component
of the chosen `inductionModuleCross`, whose total is minus the existing
physical `gridDoubleCrossComponent` with its balanced flattening.
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
It checks both occupied content and empty content. The producer and
consumer pass strict scoped checks with warnings as errors and both
compatibility settings; the consumer audits all 42 owned declarations
against the standard axiom allowlist. Full integration verification
remains separate. Canonical stored-content transport, the other
crossing fields, and the augmented inverse lift remain separate obligations.

The source head `4da876539f5147f00b608e0f0abf9f53f5808a92` passed the
full build, global axiom audit and every non-vacuity consumer in
[#1013](https://github.com/apellis/odd-lean/pull/1013)
([CI run](https://github.com/apellis/odd-lean/actions/runs/41687376775)),
merged at `73318d56`.
