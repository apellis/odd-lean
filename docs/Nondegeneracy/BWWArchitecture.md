# Brundan–Wang–Webster parameters: architecture of the extension

Topic note for Phase 2 Stage B (inhomogeneous parameters), complementing
[BWWParameters](BWWParameters.md).

## The problem

The Phase 1 theorem `OddMath.QuiverHecke.nondegeneracy_of_symmetrizer` is built on the
presentation `SKM.pres D Sc` for `Sc : SKM.Scalars D k`, whose polynomial
`Qᵢⱼ(u, v) = tᵢⱼ u^{dᵢⱼ} + tⱼᵢ v^{dⱼᵢ} + Σ_{0<p<dᵢⱼ, 0<q<dⱼᵢ} sᵢⱼ^{pq} u^p v^q`
has no pure monomials (`p = 0` or `q = 0` below the corners). Brundan–Wang–Webster
parameters (`SKM.BWWScalars`) allow them.

The pure monomials cannot be reached from the Phase 1 statement by a formal argument.
Nondegeneracy for parameters with vanishing pure part does not imply nondegeneracy for a
generic deformation without a flatness statement that is equivalent to the conclusion. So
the chain of results proving Phase 1 has to be run with the pure monomials present.

The import closure of the Phase 1 headline has about 1800 modules. About 1360 of them
mention `Scalars` or `ScalarData`. Only about 100 unfold `Qᵢⱼ`: they sum over
`Finset.Ioo 0 (D.dn i j)` or use `Sc.s`. The heaviest are the realization of the braid
relation, the bubble-slide convolution and induction, the repeated outer pure terms, the
mixed probe relations, the ψ-crossings, Lemmas 3.2–3.3 and the Chevalley relations.

## Options

* **Separate structure.** Restate the chain for `BWWScalars` and compare it with
  `toBWW`/`toScalars`. Every one of the roughly 1360 modules would have to be re-typed. This
  duplicates the chain.
* **In place (A).** Reinterpret `ScalarData.s i j p q` as the coefficient of `u^p v^q` on the
  whole box below the corners. The sums in `pres` would run over `Finset.range` instead of
  `Finset.Ioo 0`, and `Homogeneous`, `LowerDegree` and `GradedHomogeneous` would range over
  every slot below the corners. A homogeneous parameter has no pure monomials
  (`BWWScalars.Homogeneous.noPure`), so the Phase 1 headline keeps its meaning. Only the
  roughly 100 modules that unfold `Qᵢⱼ` change. The Brundan–Ellis statements for arbitrary
  parameters are recovered as one-line specializations under the predicate `NoPure`.

Option A changes the meaning of statements that were stated for arbitrary Brundan–Ellis
parameters. The maintainer chose option A.

## What holds under either option

These declarations are independent of the choice:

* `OddMath/SKM/BWWBoxSum.lean`:
  * `BWWScalars.sum_box_eq`: a box sum is the two corners, the pure monomials and the
    interior.
  * `BWWScalars.NoPure`, with `NoPure.toScalars_toBWW`, `ScalarData.toBWW_noPure` and
    `Homogeneous.noPure`.
  * `sum_box_toBWW`.
* `OddMath/SKM/BWWPresentation.lean`:
  * `SKM.presBWW`, the Kac–Moody 2-supercategory with Brundan–Wang–Webster parameters.
  * Its parity homogeneity, `isParityHomogeneous_presBWW`.
  * `presBWW_toBWW : presBWW D Sc.toBWW = pres D Sc`.
  * `presBWW_eq_pres_of_noPure`.
* `OddMath/QuiverHecke/BWWPresentation.lean`: the same for the quiver Hecke presentation.

Lemmas that need the pure monomials (bubble slides, invertibility sites, Rees reductions)
are stated against `presBWW` in new files. Under option A, `pres` becomes `presBWW`
through `presBWW_toBWW` and these lemmas are reused unchanged.

## The switch (option A, adopted)

1. `ScalarData` keeps its fields. `s i j p q` is the coefficient of `u^p v^q` on the whole
   box `i ≠ j`, `0 ≤ p < dᵢⱼ`, `0 ≤ q < dⱼᵢ`; the parity condition is unchanged.
2. The `quadNe` and `braidEq` relations of `SKM.pres` and of the quiver Hecke presentation
   sum over `Finset.range (D.dn i j) ×ˢ Finset.range (D.dn j i)`, so `pres D Sc` is the
   presentation with Brundan–Wang–Webster parameters and
   `presBWW_eq_pres : presBWW D P = pres D P.toScalars`.
3. `ScalarData.Homogeneous`, `GradedHomogeneous`, `LowerDegree` and the coefficient
   gradings quantify over `i ≠ j`, `p < dᵢⱼ`, `q < dⱼᵢ` with `sᵢⱼ^{pq} ≠ 0`.
4. Brundan–Ellis's printed parameters are the case `ScalarData.NoPure`
   (`OddMath/SKM/PureMonomials.lean`): pure monomials vanish below the corners.
   `ScalarData.Homogeneous.noPure` derives it from (1.31), and
   `ScalarData.NoPure.sum_range_range` recovers the printed interior sums.
5. Every consumer of the box sums sums over `range × range`. Where a proof used `p > 0` or
   `q > 0` for a pure monomial, the lemma carries `NoPure` as an explicit hypothesis of
   its route, supplied by `Homogeneous.noPure` at the homogeneous call sites. The
   Brundan–Wang–Webster replacements of these sites (pure coefficients in a nilpotent
   ideal) are in `BWWKind3.md` and `BWWReductions.md`.

## Pure coefficients in a nilpotent ideal (route hypothesis)

The probe dot unit (`probeMixedCorner_dot_isUnit`, `probeWord_dots_isUnit`) needs
`Qᵢⱼ(u, 0)` to be a unit when `u` is. With pure terms below the corners this holds when the
pure coefficients lie in a nilpotent ideal:

* `ScalarData.PureNilpotent Sc` (`OddMath/SKM/BWWPureNilpotent.lean`): some nilpotent ideal
  contains every pure coefficient below the corners;
  `PureNilpotent.exists_isUnit_quad_remainders` gives `Qᵢⱼ(u, v) = U + R v = U + v R'` with
  `U` a unit.
* `ScalarData.NoPure.pureNilpotent`: homogeneous parameters satisfy it (ideal `⊥`).
* `BWWReesParameters.truncated_pureNilpotent` (`OddMath/SKM/BWWReesPureNilpotent.lean`): the
  truncated Rees parameters over `k[h]/(h^N)` satisfy it (ideal `(h)`).
* `parameterTwist_pureNilpotent` and its instance: the parity transport preserves it.

The probe chain takes `[Fact Sc.PureNilpotent]`. This is a route-only intermediate
hypothesis: the homogeneous end theorems supply it from `hc.noPure.pureNilpotent` and keep
their statements, and the Brundan–Wang–Webster headline obtains it on the truncated Rees
parameters through `BWWParameterProperty.gradedCase_of_truncatedReesCase`, so it does not
appear in the headline.
