# The occupied probe weight mixed coordinates

Brundan–Ellis (1.12) requires the given weight mixed mate to retain the
constructed inverse at each occupied output coordinate. The coordinate
maps in `ELVProbeWeightMixedCoordinates` keep the literal lower block,
both successor blocks and their common upper block.

`probeOldBlockTarget_perm` and `probeOldBlockIndTo` retain an arbitrary
prescribed successor target. The object and all-map formulas
`probeOldInductionComponent_obj_of` and
`probeOldInductionComponent_map_of` identify the selected global
induction component there. The source and target object formulas then
identify both actual mixed functors with the stored-target mate's
endpoints.

`probeOldBlockDistinctCross_mixed_eq` identifies the entire selected
positive block crossing with `probeAppendToCross`. Induction reverses
the two crossing labels; commutativity of their parity product supplies
the exact degree identification. The physical quotient crossing is
unchanged. `probeOldWeightMixedCross_comparison` retains this same map
through the two specified product-coordinate equalities at every parity.

The cup and cap must still be pasted through these equalities before
using the stored-target inverse on the whole supported mixed mate.

The producer and paired concrete consumer pass the strict scoped checks.
The consumer audits all 63 owned declarations against the repository axiom
allowlist and checks the occupied coordinate maps, all-map induction formula
and selected crossing on the asymmetric mixed-parity parameters.
