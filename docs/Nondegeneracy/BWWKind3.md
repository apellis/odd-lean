# Brundan–Wang–Webster parameters: the exact form of `Qᵢⱼ(u, 0)`

Topic note for the extension to the parameters of Brundan–Wang–Webster, arXiv:2505.22929v2,
§2.2 (see `BWWParameters.md`, §5, kind 3). For Brundan–Ellis parameters

    Qᵢⱼ(u, 0) = tᵢⱼ u^{dᵢⱼ},

while for Brundan–Wang–Webster parameters

    Qᵢⱼ(u, 0) = tᵢⱼ u^{dᵢⱼ} + Σ_{p<dᵢⱼ} cᵢⱼ(p, 0) u^p.

The pure coefficients `cᵢⱼ(p, 0)` and `cᵢⱼ(0, q)` below the corners have positive coefficient
degree (`coefficientDegree_pos_of_pure`). Over a truncated Rees base they lie in a nilpotent
ideal `J`, and every argument below that uses the exact form only needs `Qᵢⱼ(u, 0)` (or its
image under a linear map) to be a unit plus an element of `J • ⊤`.

## Inventory

Declarations that use `Qᵢⱼ(u, 0) = tᵢⱼ u^{dᵢⱼ}`:

1. `ProbeReservoir.isIso_homDistinctMixedMateDot_param_sourceUnits`
   (`QuiverHecke/SwappedAssembly/Sigma/MixedEntrySourceUnits.lean`). It writes the dotted
   mate argument as `tᵢⱼ X^{dᵢⱼ} + N` with `N` admissible (every monomial has a positive power
   of `Y`). With the lower terms, `Σ_{p<dᵢⱼ} cᵢⱼ(p, 0) X^p` is not admissible. The constant
   term and the pure terms in `Y` are admissible.
   Consumer: `isIso_sigmaEntry_probe_reservoir_sourceUnits`, then
   `elvProbe_distinct_sigmaEntry_isIso` (`ELVProbeSourcePolynomialUnits.lean`).
2. `isIso_homDistinctMixedMateDot_param` (`SwappedAssembly/Sigma/MixedEntry.lean`): the same
   argument with a nilpotent reservoir dot.
3. `probeMixedCross_quadratic`, `probeMixedCross_remainder_right`,
   `probeMixedCross_remainder_left` (`CyclotomicAction/ProbeMixedRelations.lean`): these write
   `Qᵢⱼ(u, v) = tᵢⱼ u^{dᵢⱼ} + R v = tᵢⱼ u^{dᵢⱼ} + v R'`. Consumers in
   `ProbeMixedCornerRelations.lean`: `probeMixedCorner_remainders_connected`,
   `probeMixedCorner_remainders` (case `dᵢⱼ = 0`), and `probeMixedCorner_dot_isUnit` through
   `cyclotomicWordEntry_distinct_isUnit_twoRemainders`, which needs `U` to be a unit, not
   `U = tᵢⱼ u^{dᵢⱼ}`.

Checked and not of this kind:

* `appendQP_qPoly_top`, `appendQP_qPoly_above` (`ELVAppendQPLeading.lean`) use the leading
  coefficient in the `u`-degree. Every monomial other than the corner has `u`-exponent
  `< dᵢⱼ` (`BWWScalars.c_top`), so this is a box-membership statement.
* `product_source_polynomial_isUnit` (`ELVMixedSourcePolynomialUnits.lean`) uses homogeneity
  through `parameterTwist_homogeneous`; this concerns the grading, not `Qᵢⱼ(u, 0)`.
* The same-colour mates (`RouquierHomPostMateUnits`, `RouquierHomPostInverseUnits`,
  `SwappingReservoir`, `RouquierHomDistinctMixedPostDotsComp`) do not involve `Qᵢⱼ`.

## Replacements

Checked declarations:

* `OddMath/Algebra/NilpotentPerturbationRing.lean`: for a `k`-algebra `R` and a nilpotent
  ideal `J` of `k`, elements of `J • ⊤` are nilpotent (`isNilpotent_of_mem_smul_top`), a unit
  plus such an element is a unit (`isUnit_add_of_mem_smul_top`), and
  `t u^d + Σ_{p<d} c_p u^p` is a unit for `t` a unit, `u` a unit and `c_p ∈ J`
  (`isUnit_smul_pow_add_sum`).
* `OddMath/Algebra/BoxPolynomialUnits.lean`: the box sum `Σ_{p≤d, q≤d'} c(p,q) u^p v^q`
  splits into its row `q = 0` and a remainder divisible by `v` on either side
  (`sum_box_split`, `sum_box_eq_add_mul`, `sum_box_eq_add_mul_left`, the latter under a
  signed slide `u^p v = ε^p v u^p`), and `exists_isUnit_box_remainders` gives
  `Q = U + R v = U + v R'` with `U` a unit.
* `OddMath/SKM/BWWPureCoefficients.lean`: `BWWScalars.PureIn Sc J` (pure coefficients in
  `J`), proved for graded-homogeneous parameters (`PureIn.of_gradedHomogeneous`) and for
  Brundan–Ellis parameters (`PureIn.of_toBWW`, any `J`); `isUnit_lowerPoly` and
  `exists_isUnit_quad_remainders` specialize the two results above to `Qᵢⱼ`.
* `OddMath/QuiverHecke/SwappedAssembly/Sigma/BWWMixedEntry.lean`:
  `ProbeReservoir.isIso_homDistinctMixedMateDot_bwwParam_sourceUnits` replaces item 1 for the
  box sum of `presBWW`. The lower terms map into `J • ⊤` by linearity of the dotted mate and
  are absorbed by `OddMath.Algebra.isIso_add_of_mem_smul`. The case `dᵢⱼ = 0` needs no
  separate argument.

## Remaining

* Item 2 (nilpotent reservoir dot): the same proof applies once the consumer needs it.
* Item 3: `exists_isUnit_quad_remainders` applies in the cyclotomic corner ring once the
  Brundan–Wang–Webster category is in place (`BWWArchitecture.md`). The left remainder uses the
  signed slide of the probe dot past the reservoir dot.
* Nothing here changes the truth of the statements: the lower terms enter only through a
  nilpotent perturbation of a unit.
