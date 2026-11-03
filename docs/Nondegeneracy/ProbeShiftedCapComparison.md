# Prescribed scalar caps with canonical parity targets

Source: DeformedMatrixComparison (2), (5), and the canonical shifted finite
families implementing Brundan--Ellis (1.13)--(1.14).

`shiftedCapDotRow` is the existing `capDotRow` followed by the given target
parity-coordinate inverse. It is even. `shiftedCapDotRow_total` identifies
its actual module component with the raw `shiftedCapDotLinear`; both use the
full canonical parity-module action.

`parityRestrictionIso_inv_coordinate_total` evaluates the checked canonical
parity/restriction square. `shiftedCapDotLinear_compare` attaches these
coordinates to an unshifted row comparison for two possibly different
induction functors. No dotted row is rescaled or redefined.

For the selected scalar comparison, `probeMappedAppendLinear_capDotRow`
identifies the existing all-power counit comparison with the actual
module dot/counit rows. `probeMappedAppendLinear_shiftedCapRow` then compares
every prescribed row at its actual canonical shifted target through
`parityRestrictionIso`. All premises are discharged by the scalar module
restriction equality; no cap-compatibility assumption is introduced.

`capMatrixEntry_some_eq_shiftedCapDotRow` binds the generic shifted row
literally to the existing old finite cap-matrix field. Its already proved
normalized kernel formula remains unchanged, including the whole output
parity involution and twisted actions in source equation (5). The original
old representable is never assumed to evaluate coefficients through the
scalar quotient.

The paired consumer checks both moving parities on mixed regular modules,
all powers, vacuum, actual old/ordinary row totals and evenness, and the
literal matrix-field binding on old representables. The strict producer
and consumer checks pass; the consumer audits all 47 owned declarations
against the repository axiom allowlist.

Remaining matrix work: the first (mate) slot, source/target content charts,
and whole finite inverse assembly must use the same prescribed entries.
This batch establishes the dotted cap slots and their parity targets; it
does not assert a completed matrix inverse.
