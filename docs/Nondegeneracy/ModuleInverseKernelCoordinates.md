# Module inverses in balanced kernel coordinates

For the finite matrix comparison in DeformedMatrixComparison §4 and the inverse degree step G8, `moduleUnitMatrixIso_inv_tensor` and `moduleCapMatrixIso_inv_tensor` identify the selected OLD module inverse on each balanced pure tensor with the inverse of the actual coefficient matrix. The module vector is retained. No flatness or projectivity assumption is added.

`moduleUnitMatrixIso_principal_inv_tensor` removes the prescribed principal parity shift and evaluates the raw `positiveKernelPrincipalInverse`. `moduleCapMatrixIso_principal_inv_tensor` inserts the literal upper-Hom coefficient in `Option.none` and evaluates `negativeKernelPrincipalInverse`. These are the same raw maps whose intrinsic integer degrees are proved in `ELVKernelMatrixInteger`.

The producer and paired consumer pass strict scoped checking. The consumer covers both moving parities, positive and negative heights, empty windows, and an independently detected nonzero odd input tensor whose selected module inverse is nonzero. All eight owned declarations pass the standard axiom allowlist audit. Full package CI remains the integration gate.
