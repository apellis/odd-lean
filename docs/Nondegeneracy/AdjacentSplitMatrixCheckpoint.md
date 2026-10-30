# Occupied adjacent split matrix: verification checkpoint

Branch: `research/odd-nondegeneracy-adjacent-split-matrix-1030`.
PR: https://github.com/apellis/odd-lean/pull/652 (depends on #649).
Checked mathematical checkpoint: `cf4f7c007615158bee0e290ee549d4b962634384`.
The subsequent changes are **WIP default-source elaboration repairs**, not a
new mathematical claim. Do not merge until the current head is verified.

## Proved scope

`adjacentSplit_braid` assembles all four literal `i i j → j i i` entries for
arbitrary source/target paths at the endpoint with one repeated-colour
reservoir and two probes. It preserves `c.IsInverse` and `CrossCoeffInputs`.
The J entry uses the existing Q-weighted rectangle; square and conjugate
entries cancel only comparison isomorphisms. Other endpoint patterns,
pure-reservoir braids, repeated-outer corrections, complete CrossBraid and
nondegeneracy remain separate.

## Checks at the checked checkpoint

- `lake --wfail build OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentSplitBraid`: passed, using the repository's existing package options.
- `lake env lean -DwarningAsError=true scripts/NonVacuity/AdjacentSplitMatrix.lean`: passed with default consumer options.
- Owned-declaration audit: Matrix 15 declarations (3 private), Reduction 4,
  Braid 10; only `propext`, `Classical.choice`, `Quot.sound`.
- Declaration-clash check and source-copy check: passed.
- Independent mathematical review: accepted exact endpoint scope, signs,
  retained Q factors, actual classification and absence of assumed transport.
- GitHub full build was still in progress on the checked checkpoint.

## WIP checks and next step

Direct default-option source checks, beyond the passing default consumer,
exposed elaboration issues. Targeted `erw` repairs are preserved in
`AdjacentSplitMatrix`; formatting and documentation improvements are also
preserved. The package build has not been rerun after these edits.

Each command `lake env lean -DwarningAsError=true
OddMath/QuiverHecke/SwappedAssembly/BraidMixed/<module>.lean` failed:

- `AdjacentSplitMatrix`: remaining heterogeneous endpoint simplification in
  `adjacentSplit_probe_heq`.
- `AdjacentSplitReduction`: simplification after the evaluated sums does not
  match under default transparency.
- `AdjacentSplitBraid`: raw-rectangle simplifications and entry-reduction
  rewriting do not match under default transparency.

The joint import with `ELVContentExactness` did not run successfully: its local
object file was absent, not a detected declaration clash.

Next: finish the bounded typed endpoint/rectangle elaboration repairs without
adding option overrides or increasing limits, rerun the scoped package build
and default consumer/audit, then the available joint imports. Check GitHub's
full build on the final head. Do not run a local full-root build.
