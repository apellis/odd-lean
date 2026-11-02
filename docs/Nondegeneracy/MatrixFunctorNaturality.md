# Input-module naturality of the whole prescribed matrices

**Verification boundary.** All three producers and both paired consumers
pass strict scoped checks. All owned declarations
pass the axiom allowlist: 26 generic, 24 finite-family naturality and 14
content inverse declarations. Full CI remains a separate gate.

This supplies the finite-family assembly step of
[DeformedMatrixComparison](DeformedMatrixComparison.md), section 4.
The construction retains the literal parity-shifted ordinary unit/cap
entries and ordered crossing mate of `ELVMatrixEntryNaturality`.

`FiniteSupermoduleFunctor.productMap` applies each coordinate's two
homogeneous components independently. Its composition and parity formulas
hold for arbitrary supernatural module maps. Finite even columns and rows
commute with this coordinate map whenever their individual entries do.
In particular there is no assumption that an input-module map is even.

`ELVMatrixFunctorNaturality.unitMatrixSourceFunctor` and
`capMatrixTargetFunctor` use exactly the previous finite source and target
modules as their objects. Their coordinate maps use only the explicit
endpoint equalities from the prescribed summand functors. Both functors
are additive, linear and parity preserving. `unitMatrixModuleNatTrans`
and `capMatrixModuleNatTrans` then assemble the literal finite matrices.
`ELVContentMatrixFunctorInverse` provides the `_total` lemmas identifying
their full forward components without a change of normalization.

Restricting the output to one content makes its count constant.
`contentUnitMatrixFunctorNatIso` and `contentCapMatrixFunctorNatIso`
use the previously proved content-module isomorphisms as components.
Whole-matrix input-module naturality gives naturality of their inverses
as well. This includes both height signs, both moving parities, and
height zero with no finite dotted entries. The coefficients remain the
full exterior coefficients.

The paired consumers use mixed-colour representables, permuted output
words, both moving parities, both signs, nonempty negative-height finite
families, zero counts, even inverse components and inverse naturality.
The module is not yet identified with the chosen fixed-content E/F composites or the original-weight functors; those comparisons and
their chosen generator/adjunction transports remain separate obligations.
