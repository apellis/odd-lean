# Odd nondegeneracy: mathematical handoff

## Research objective and order

**Phase 1 is proved.** `QuiverHecke.nondegeneracy_of_symmetrizer` proves
the conjecture for every symmetrizable Cartan superdatum, every commutative
ring with 2 invertible, every homogeneous scalar system and every supplied
`CScalars`, with no further hypotheses; the swapped route, exact heads and
integration evidence are in [STATUS](STATUS.md). Do not pursue
nonsymmetrizable Cartan data. The branch is complete when the odd analog and
its checked all-even specialization recover the most general cited even
nondegeneracy theorems over rings with 2 invertible; see
[FieldScopeBoundary](FieldScopeBoundary.md) for the parameter benchmark and
completion checks.

**Phase 2 is proved** for the parameters of Brundan–Wang–Webster,
arXiv:2505.22929v2, §2.2: `QuiverHecke.bwwLowerDegreeNondegeneracy` and
`QuiverHecke.bwwGradedNondegeneracy` (#1151), given `CScalars`.

Next mathematical targets, in order:

1. **All-even comparison.** At parity identically zero, identify the
   presentation, normalizations, decorated matching families and bubble
   coefficients with the ordinary Kac–Moody 2-category of the even
   benchmark, and recover its basis theorem (including the grading). Checked (#1152):
   the parity-zero specialization `bwwPolynomials_evenNondegeneracy`, BWW (2.11),
   the graded basis `bwwPolynomials_evenGradedNondegeneracy` (with `c` in degree
   zero) and `bwwPolynomials_evenDirectSum`. Remaining: identification of the other
   relations with an independent even object for general `Q`
   ([BWWEvenComparison](BWWEvenComparison.md)). #1059 compares conclusions only.
2. **Normalizations.** Supply compatible `CScalars` under the benchmark's
   realization hypotheses, or prove a change-of-normalization comparison.
   Deferred by decision: for dependent simple roots `CScalars` may not exist
   (`RootCover.nonempty_cScalars_iff`; affine `A₁` with `t₀₁ = 2`), so the
   theorem can be vacuous there. This gap is recorded in STATUS, not worked on.

Start with [STATUS](STATUS.md) for established scope and claim boundaries.
[SwappedNondegeneracy](SwappedNondegeneracy.md) is the written proof.
The Lean proof runs through the vacuum route of #1056, whose hypotheses the
swapped bubble fields supply (proof-structure table in [STATUS](STATUS.md)).
Earlier dependency analyses are in git history.

## Phase 2 route

The BWW headlines run: Rees parameters over `k[h]` (`SKM.nondegeneracyConjecture_of_lowerDegree`),
separating truncations `K[h]/(h^N)` (`nondegeneracyConjecture_of_separating`), and the graded
base `QuiverHecke.nondegeneracy_of_graded_base`, whose sector inputs hold over a base graded in
degrees `0, …, b`. The route-only hypothesis `ScalarData.PureNilpotent` is supplied by the
truncations and does not enter the headlines. Symmetrizability is retained; no route for
nonsymmetrizable data is to be developed. See [Phase2Plan](Phase2Plan.md) and
[FieldScopeBoundary](FieldScopeBoundary.md).
