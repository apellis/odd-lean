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

Next mathematical targets, in order:

1. **All-even comparison.** At parity identically zero, identify the
   presentation, normalizations, decorated matching families and bubble
   coefficients with the ordinary Kac–Moody 2-category of the even
   benchmark, and recover its basis theorem (including the grading) from
   `nondegeneracy_of_symmetrizer`. #1059 compares conclusions only.
2. **Phase 2.** Inhomogeneous parameters for symmetrizable data, covering
   the graded-coefficient generality of Brundan–Wang–Webster,
   arXiv:2505.22929v2, Theorem 5.6. First decide how the present `Scalars`
   presentation extends to positive-degree coefficients, then check which
   steps of the swapped route use `Sc.Homogeneous`.
3. **Normalizations.** Supply compatible `CScalars` under the benchmark's
   realization hypotheses, or prove a change-of-normalization comparison.
   Deferred by decision: for dependent simple roots `CScalars` may not exist
   (`RootCover.nonempty_cScalars_iff`; affine `A₁` with `t₀₁ = 2`), so the
   theorem can be vacuous there. This gap is recorded in STATUS, not worked on.

Start with [STATUS](STATUS.md) for established scope and claim boundaries.
[SwappedNondegeneracy](SwappedNondegeneracy.md) is the written proof.
The Lean proof runs through the vacuum route of #1056, whose hypotheses the
swapped bubble fields supply (proof-structure table in [STATUS](STATUS.md)).
Earlier dependency analyses are in git history.

## Phase 1 field endpoint and Phase 2 boundary

The field construction retains `sy : Symmetrizer D` and homogeneous
parameters and furnishes the characteristic-zero field case of the conjecture;
the ground-ring theorem then supplies ordinary rings with 2 invertible.
Homogeneity is relaxed only in Phase 2; symmetrizability is retained in both
phases. For Phase 2, specify the graded-coefficient/inhomogeneous parameter
presentation, prove the required extension and scalar comparisons, and check
the all-even specialization against the cited even benchmark. No proof route
for nonsymmetrizable data is to be developed. See
[FieldScopeBoundary](FieldScopeBoundary.md).

Phase 2 target: `SKM.GradedCoefficientNondegeneracy D sy`
([GradedParameters](../../OddMath/SKM/GradedParameters.lean)). It already
implies the lower-degree ungraded statement
(`SKM.nondegeneracyConjecture_of_lowerDegree`). Next targets, in order
([Phase2Plan](Phase2Plan.md)): the reduction to the universal ring, to
characteristic-zero fields and to the truncated Rees parameters over
`K[h]/(h^N)` is checked; what remains is
`TruncatedRees.TruncatedReesNondegeneracy D sy`. Grade the KLR category over
`K[h]/(h^N)` as a `K`-linear supercategory with `h` in degree one (design in
Phase2Plan, step 2: coefficient-graded presentations and restriction of
scalars, `GradedSupercategory` unchanged; items 1–3 are checked:
`Diagrams.CoefficientGrading`, `QuiverHecke.isHomogeneous_coefficientGraded`,
`QuiverHecke.isHomogeneous_rees`, `Diagrams.Supercategory.restrictScalars`,
bundled as `Diagrams.CoefficientGrading.gradedSupercategory` and
`QuiverHecke.reesGradedSupercategory`, and over the truncations
`QuiverHecke.truncatedReesGradedSupercategory`);
rerun the nilpotence, kernel-degree and inverse-degree arguments of the field
route over such bases. The associated graded gives only spanning and is not
a route to independence. The missing pure monomials `u^r`, `v^s` of BWW are a
recorded open statement decision; `Scalars` is not enlarged.
