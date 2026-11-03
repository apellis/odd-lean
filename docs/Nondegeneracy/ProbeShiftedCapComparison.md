# Proposed shifted scalar cap comparison

Target: DeformedMatrixComparison (2), (5), including the canonical target
parity shifts in the prescribed cap matrix fields.

This snapshot is PROPOSED, not a checked library batch. Its generic
`shiftedCapDotRow` is exactly the given `capDotRow` followed by the canonical
parity-coordinate inverse. The generic comparison uses the checked
parity/restriction bridge and an explicit unshifted cap-row equation.
The first strict check failed only at the restriction component conversion
in `parityRestrictionIso_inv_coordinate_total`; no budgets or axioms were
changed. It has no export and no paired consumer yet.

Next: repair that generic component conversion before specializing; attach
the actual selected scalar cap-row theorem to `capDotLinear`, then the
shifted row comparison, and add mixed even/odd and vacuum consumers. Keep
the normalized old kernel field binding and full parity-module actions
explicit. The original old representable is not assumed to evaluate
coefficients through the scalar quotient.
