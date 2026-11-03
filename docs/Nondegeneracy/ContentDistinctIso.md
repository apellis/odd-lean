# The homogeneous inverse on untruncated old-content modules

This bundles the pointwise coend inverse in
[ContentDistinctMate](ContentDistinctMate.md) as a homogeneous module
inverse and an inverse supernatural in arbitrary input modules. The
scope is the unweighted, untruncated category
`Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)`.

For lower functors J:C→A and K:C→B and upper functors L:A→E and M:B→E,
the source on input modules is `restriction J ⋙ induction K`; the target
is `induction L ⋙ restriction M`. The upper unit and lower counit are
ordinary even adjunction maps. The crossing has parity p. Composing these
supernatural families proves
`orderedRectangularMateComponent_supernatural`, with parity p even on
odd input-module maps.

`ELVRectangularMateIso` assembles pointwise bijectivity of this fixed raw
map before specializing the four categories. The constructor
`HomogeneousSuperfunctorIso.ofHom` preserves its forward map exactly and
gives inverse parity p. It is used once for module isomorphisms and once
for the superfunctors on input modules.

The concrete `ELVContentDistinctIso` supplies every bijectivity input from
`oldContentDistinctMateLinear_bijective`. Thus its only colour hypothesis
is i≠j; no additional inverse hypothesis is imposed.
`oldContentDistinctMateModuleIso` is an isomorphism of old-content
modules. Its forward equality is `oldContentDistinctMateModuleIso_hom`,
and its inverse has crossing parity p(i)p(j) by
`oldContentDistinctMateModuleIso_inv_mem`.

`oldContentDistinctMateFunctorIso` is an isomorphism of the two
superfunctors on input modules. The whole forward transformation is
identified by `oldContentDistinctMateFunctorIso_hom`, and each total
component is exactly the independently prescribed content
cup-crossing-cap by `oldContentDistinctMateFunctorIso_hom_total`.
`oldContentDistinctMateFunctorIso_inv_mem` retains the same crossing
parity in the inverse. Its supernatural law includes arbitrary odd
input-module maps.

Both producers and the paired consumer pass strict scoped checks,
auditing all 42 owned declarations. The consumer uses shifted old
representables, both mixed moving parities, distinct odd colours, zero
cutoff with empty lower content, both inverse identities, and signed
inverse naturality on an odd parity-change map. Full CI remains the
integration gate.

Canonical coefficient-truncated ContentModules and original-weight
transport remain subsequent obligations. This batch bundles the
untruncated old-content inverse already obtained from the chosen E/F
chart square; it does not change that prescribed forward map.
