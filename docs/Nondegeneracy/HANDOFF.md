# Odd nondegeneracy: open questions and restart

The proved results are listed in [STATUS](STATUS.md). The scope is fixed by
[FieldScopeBoundary](FieldScopeBoundary.md): symmetrizable Cartan superdata,
ordinary commutative ground rings with `2` invertible, and the parameters of
Brundan–Wang–Webster, arXiv:2505.22929v2, §2.2. Do not pursue
nonsymmetrizable data.

## Open question

**Normalizations for dependent simple roots** (deferred by the
maintainer). The headline theorems take `cs : CScalars Sc` as an argument.
A normalization exists exactly when the condition of
`RootCover.nonempty_cScalars_iff` holds, so for dependent roots (affine
`A₁` with `t₀₁ = 2`) the theorems can be vacuous. A change-of-normalization
comparison would remove this restriction.

When `2` is not a unit the presentation includes the integral relations
`Rel.zInt`, and the theorem over every commutative ring is
`QuiverHecke.integral_nondegeneracy_of_symmetrizer`; with `2` invertible
these relations hold automatically.

The all-even comparison is closed (BWW (2.11) checked formally, the other
relations by inspection; [BWWEvenComparison](BWWEvenComparison.md)).

## Restart

- Read [STATUS](STATUS.md), then the written proof
  [SwappedNondegeneracy](SwappedNondegeneracy.md) and, for Phase 2,
  [Phase2Plan](Phase2Plan.md).
- The Lean proof runs through the vacuum route; the proof-structure table in
  [STATUS](STATUS.md) lists each reduction with its module.
- The branch is to be merged into `master` after the cleanup recorded in
  [Cleanup](Cleanup.md); that file also lists the merge procedure.
