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
allowlist audit. Full build, axiom audit and all concrete consumers passed in #952.

`ELVContentMatrixInverse` now implements the output-content naturality step.
`unitMatrixSourceModule` and `capMatrixTargetModule` use the pointwise
superspace product of the prescribed shifted families. `unitMatrixNatTrans`
and `capMatrixNatTrans` assemble their even module entries naturally along
all old-category arrows, including inhomogeneous arrows. Restricting to a
fixed output permutation class makes the finite count constant.
`contentUnitMatrixNatIso` and `contentCapMatrixNatIso` assemble the verified
components and their inverses into ordinary natural isomorphisms.
`contentUnitMatrixIso` and `contentCapMatrixIso` lift these to even
supermodule isomorphisms. Their `_hom_total` lemmas identify the literal
matrix components, and `_even` checks both directions as module morphisms.

This step is scoped-checked with a mixed-colour consumer, including arbitrary
old input modules, both moving parities, reordered output words, inverse
naturality, height zero and the axiom allowlist. Full CI passed in #953 and
in the integrated research-head check for #954.
It concerns output-arrow naturality of the restricted old-category matrices.
It does not establish naturality in input-module maps or identify the source
and target with the chosen fixed-content E/F composites.

`ELVMatrixEntryNaturality` supplies the next input-module step. The actual
induction-dot powers, ordinary dotted units and caps, and fixed ordered mate
are homogeneous supernatural families in the input module. The source and
target parity shifts yield `unitMatrixEntryNatTrans` and
`capMatrixEntryNatTrans` on the entire old module category, including odd
and inhomogeneous module maps. Their component comparison lemmas retain
explicit endpoint equalities with the existing finite matrix entries;
there is no entry rescaling. The summand functors are additive, linear and
parity-preserving.

This entry-level step and its mixed representable consumer pass strict local
checks and the owned-declaration axiom audit. The integrated research head
`f070980ac0a0ba23b6faf79dd53faaadfce27aa2` passed
[full CI](https://github.com/apellis/odd-lean/actions/runs/41489136665). Naturality
of the assembled matrix and its inverse in the input module still needs
finite-family map assembly; entry-level naturality alone is not a bundled
natural isomorphism of module functors.

Next, compare these old-category module components with the actual fixed-content
and original-weight functors, retaining their chosen dot, crossing and adjunction
normalizations. This result supplies neither a completed full-ELV factor action
nor nondegeneracy by itself.
