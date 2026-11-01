# Scalar representation factorization on actual old probe modules

`ELVProbeScalarModules.lean` proves that the actual old probe module
evaluates every full quotient coefficient by the prescribed binomial scalar
evaluation. The condition includes the entire exterior algebra.

`probeOldModuleRawAction_factor` then proves that any old module satisfying
that condition acts on every raw old arrow through its literal scalar Hom
specialization. The proof uses the tensor universal property and the
existing unit-affine-prefix composition formula. It requires no flatness,
PBW decomposition or separately assumed tensor-kernel identity.

The concrete producer is `probeOldModule_evaluatesCoefficients`.
The closed mixed odd/even consumer pairs an odd exterior coefficient with
an odd affine dot and proves its action is zero. A second example checks
the prescribed elementary coefficient acts by the binomial scalar -3.
Strict local producer/consumer checks and all 23 owned axiom audits pass.
Full CI remains the integration gate.

This is a representation factorization for the untruncated old category.
Closure under old append induction and descent to the ordinary cycHom
quotient are separate successors. No scalar specialization of a weighted
coefficient truncation is asserted.
