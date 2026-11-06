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

Option A changes the meaning of statements that are currently stated for arbitrary
Brundan–Ellis parameters. It is therefore a maintainer decision and is not yet adopted.

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

## Under option A: the switch

1. `ScalarData` keeps its fields. `s` becomes the full box coefficient below the corners,
   and the parity condition is unchanged.
2. `relation`: the `quadNe` and `braidEq` sums use the box sums `quadSum`/`braidSum` of
   `SKM.BWWPresentation`, with `c` assembled from `t` and `s`.
3. `ScalarData.Homogeneous` and the graded variants quantify over `0 ≤ p < dᵢⱼ`,
   `0 ≤ q < dⱼᵢ`.
4. The roughly 100 modules that unfold `Qᵢⱼ` are rewired: an interior sum becomes a box sum
   via `sum_box_eq`. The pure contributions are discharged by the lemmas proved against
   `presBWW`.
5. Brundan–Ellis statements for arbitrary parameters become corollaries under `NoPure`,
   where the presentation is literally the old one (`presBWW_eq_pres_of_noPure`).

The switch is a single change, checked by complete builds that run every module before it
is merged.
