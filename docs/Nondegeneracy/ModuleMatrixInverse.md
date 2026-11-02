# Prescribed same-colour inverses on arbitrary modules

This implements the arbitrary-module tensor transfer of
[DeformedMatrixComparison](DeformedMatrixComparison.md), section 4.
It uses the prescribed old-category module matrices, without identifying
these with the still-unfinished full weight-level action.

The target-content count gives pointwise bijective ordinary-right coefficient
kernels in `ELVKernelMatrixBijective`. Balanced tensoring preserves this
isomorphism on every old supermodule. Canonical quotient and finite-family
coordinates then identify the forward maps with `unitMatrixComponent`
and `capMatrixComponent`, by the previously checked whole-forward identities.
No tensor flatness or arbitrary-kernel evenness premise is required.

`ELVModuleMatrixInverse` defines `moduleUnitMatrixIso` for nonnegative
content crossing height and `moduleCapMatrixIso` for nonpositive height.
Both apply at height zero, with empty finite families. The `_hom` lemmas
identify the literal prescribed forward maps; `_hom_even` and `_inv_even`
retain the exact SVec parity profiles. Inverse parity follows from the
verified forward parity and the two inverse identities.

The source, paired mixed-data consumer and public umbrella export pass strict
local checking.
The consumer proves height conditions for both moving parities, identifies
the literal forward maps, checks inverse evenness and the empty-row case,
and audits every owned declaration. Both inverse products are checked on concrete mixed representable modules.
All 17 owned declarations, including private/generated ones, pass the axiom
allowlist audit. Full repository CI remains the integration gate.

Next, compare these old-category module components with the actual fixed-content
and original-weight functors, retaining their chosen dot, crossing and adjunction
normalizations. This result supplies neither a completed full-ELV factor action
nor nondegeneracy by itself.
