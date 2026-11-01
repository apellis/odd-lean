# Finite coefficient families and arbitrary-module kernel tensor

`BalancedKernelTensor.piEquiv K M` proves that tensoring a pointwise finite product indexed by a small type of ordinary-right coefficient kernels with an arbitrary SVec-valued module is linearly equivalent to the finite product of their literal balanced kernel tensors. It applies in particular to Option(Fin m), including m=0.

The product kernel, coordinate projections/injections, quotient forward map and finite summed inverse are explicit. `piEquiv_tensor` gives each forward coordinate on a quotient generator; `piEquiv_symm_single` gives the inverse of a single coordinate. Both inverse identities are proved through the balance quotient. No flatness, projectivity, field, additive-kernel or finite-object-category hypothesis is used.

The exact producer and concrete Option(Fin 2) consumer passed strict local checks; all 26 owned declarations, including private/generated, were audited. The consumer uses three heterogeneous actual Hom kernels and the full mixed-parity old representable, and checks the generator, single-coordinate inverse and whole-vector inverse formulas. The consumer also checks the Option(Fin m) API at arbitrary coefficient/category universe u, so no equality between the finite index universe and u is assumed. Full branch CI remains required before integration.

Scope: this is the underlying ground-ring finite-family tensor equivalence. Kernel grading and normalized-matrix ordinary-right covariance are separate prerequisites for its attachment to the actual shifted action families; this result alone is not the arbitrary-supermodule matrix theorem.
