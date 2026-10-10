# odd-lean

A Lean 4 / Mathlib formalization of odd symmetric functions, the odd nilHecke algebra and the odd
Littlewood–Richardson rule, together with machine-checked errata to the source papers.

Sources (numbering refers to these arXiv versions):

- **[EK]** A. P. Ellis, M. Khovanov, *The Hopf algebra of odd symmetric functions*,
  arXiv:1107.5610v2.
- **[EKL]** A. P. Ellis, M. Khovanov, A. D. Lauda, *The odd nilHecke algebra and its
  diagrammatics*, arXiv:1111.1320v1.
- **[E]** A. P. Ellis, *The odd Littlewood–Richardson rule*, arXiv:1111.3932v1.
- **[EQ]** A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2
  (Thm 3.18 and Thm 4.17 are proved, over every field and over `ℤ`; three numbered statements are
  formalized only in part, see the [EQ] coverage table below).
- **[BE2]** J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2 (in
  progress; see the [BE2] status below).

The library builds with no `sorry` and no added axioms; the axiom closures of the results contain
only `propext`, `Classical.choice` and `Quot.sound`.

## Status

**[EK], [EKL] and [E] are formalized in full**, with the carve-outs listed below. Every theorem,
proposition, lemma, corollary, displayed equation, worked example and precise remark of the three
papers is a Lean theorem about the library's objects, or, where the printed statement is false, the
printed statement is refuted in Lean and the corrected statement is proved. The false statements, misprints and proof gaps are
listed in [ERRATA.md](ERRATA.md), each with the declarations that refute and correct it. Signs and
conventions are taken exactly as printed; every corrected statement is a separate declaration.

Names below are in `OddMath.Frontier` unless they start with `Diagrams.`, which are in `OddMath`.
Files named `*Audit.lean` restate headline results and print their axioms; `*Controls.lean` and
`OddMath/Tests/*` contain finite checks.

### [EK]

Modules `EK*` (with `ErrataChecksEK*`). Scope and carve-outs:

- Ground ring: [EK] works over an arbitrary commutative ring k. §2.1 (the form, the radical, the
  q-bialgebra Λ′) is formalized for every k and q; from §2.2 on (q = −1) results are proved over ℤ
  and transported to every k (`EKOverK*`, `EKGeneralQBaseChange`, `EKFinalBaseChange`). Where a
  statement needs 2 ≠ 0 in k, or characteristic 0 (§3.2, formalized over every ℚ-algebra), the
  exact hypothesis is proved; see [ERRATA.md](ERRATA.md).
- §2.4: NΛ_q and QΛ_q are realized as Λ′ and the free module on compositions with the quantum
  quasi-shuffle product, in perfect duality; QΛ_q is proved to be a q-bialgebra.
- Omitted: the numerical data tables of the appendix (§5) are not a target. Most of their entries
  are nonetheless checked (the §5.1 tables, the §5.2 table at q = −1 in degree 6, the general-q table
  in degrees ≤ 4, and the Gram determinants in degrees ≤ 6); the factorization of the degree-7 Gram
  determinant is not. The general statements of §5.2 (nondegeneracy over ℚ(q), the degree (5.1)–(5.2)
  and the leading coefficient) are proved in every degree. The intermediate counts in
  Examples 4.4–4.7 are not restated beyond the RSK correspondences themselves.

### [EKL]

Modules for §2 (`EKLSectionTwo*`, `OddSchubertAction`, `CenterCorrected`, `OwlGeneral`, `SchubertBasis`,
…), §§3–4 (`ZeroHecke`, `OnhReflection`, `StrandCrossing`, `Thick*`, `ShuffleLemma`, `Staircase*`,
`MonomialReversal`), §5 (`Cyclotomic*`, `OddGrassmannSchur`, `OddSymmetricLimit`), §6
(`OnhStructure*`, `Categorification`, `GradedK0*`, `QuantumSl2Plus`, `OddCategorification*`,
`OddBialgebra*`, `OddCyclotomicAction*`), ranks 0 and 1 (`SmallRank*`), and `EKLMisc*`, `EKLGaps*`.
Scope:

- Every rank a ≥ 0: statements in rank a = n + 2 live on `NilHeckeAction.Presented n`; ranks 0 and 1
  are covered separately in `SmallRank*`. Coefficients are in ℤ.
- Diagrams are interpreted as elements of the odd nilHecke ring, which acts faithfully on the odd
  polynomial ring; thick calculus is proved in the ring. The diagrammatic presentation itself
  (relations (2.7)–(2.10) and the equivalence with `Presented n`) is in `Diagrams.OddNilHecke`, built
  on [string-diagrams-lean](https://github.com/apellis/string-diagrams-lean).
- §6: K_0 is the Grothendieck group of finitely generated graded projective modules, presented by
  graded idempotent matrices up to Murray–von Neumann equivalence (`GradedK0`). Induction and
  restriction are constructed on all graded idempotents; they give the q-bialgebra structure on
  K_0(ONH) (with braiding parameter q^{-2}) and the U_q(sl_2) action on K_0(ONH^N), identified with
  the integral form of V(N). F is realized as restriction along ONH_a^N → ONH_{a+1}^N followed by a
  grading shift; the odd two-step flag bimodules enter through the corresponding relation in
  OPol_a, not as separately constructed bimodules. The Morita equivalences are equivalences of
  module categories (ungraded, as in the paper); the classification of indecomposable graded
  projectives is stated in the idempotent-matrix model.
- The open question in the corrected form of Lemma 2.18 (whether the conclusion holds for reduced
  words outside the class for which it is proved) is recorded in [ERRATA.md](ERRATA.md).

### [E]

Modules `OddLR*` (with `ErrataChecksE`). Scope:

- Every number of variables N ≥ 0, including the plactic algebra on the infinite alphabet.
- The classical theory of §4.1 is formalized in the q = 1 specialization of [EK]'s Λ, with Schur
  functions defined by Kostka inversion; there is no separate comparison with a Mathlib ring of
  symmetric functions (none exists at the pinned Mathlib).
- Polytopes and cones (§4.3) are over ℝ; lattice-point statements over ℤ.

### [EQ] (partial)

The differential `d(x_i) = x_i²`, `d(∂_i) = 1` is constructed intrinsically on the diagrammatic
category, as the derivation induced by a local derivation compatible with the defining relations,
over any commutative ring; it is then transported to `Presented n` (rank `n+2`). Indices start at
`0`, and `{m} = m mod 2`.

- Compatibility of `δ(dot) = x²`, `δ(crossing) = 1` with the relations:
  `Diagrams.OddNilHecke.compatible`.
- `d(x_i) = x_i²`, `d(∂_i) = 1`, Leibniz (2.3), `d² = 0`, `d` odd: `Diagrams.OddNilHecke.d_x`,
  `d_ψ`, `d_mul_of_mem`, `d_d`, `deriv_mem_homDeg`; on `Presented n`: `Diagrams.OddNilHecke.dONH_dot`, `dONH_crossing`,
  `dONH_mul`, `dONH_dONH`, `dONH_mem_parity`.
- Prop 3.3 as printed (the differential induced from `OPol_n(α)` is local iff `α ∈ {(0,1,0,1,…), (1,0,1,0,…)}`, and then
  `d(∂_i) = 1`): `EQFix.prop_3_3`, `prop_3_3_iff`. (2.20), (2.22): `EQFix.longestPerm_elementary`, `eq_2_22`.
- Prop 3.3, intrinsic variant: the ansatz (3.7) is compatible iff `a = 1`, `b = c = 0` (over ℤ):
  `Diagrams.OddNilHecke.ansatz_compatible_iff`. Prop 3.3 as printed concerns the differential induced
  from a dg module `OPol_n(α)`; the formalized statement instead characterizes the local ansatz by
  compatibility with the defining relations. Its linear constraints coincide with (3.9)–(3.10) after
  substituting (3.8).
- Lemma 3.4, (3.13): `Diagrams.OddNilHecke.d_longest`, `dONH_DElem`.
- Lemma 3.5, (3.16) and (3.17): `Diagrams.OddNilHecke.d_idem`, `d_staircase`, `dONH_eqIdempotent`.

§2.1 (`Frontier.EQQuantum*`, over `ℤ[√−1]`): `U⁺` and `u⁺` at `q = √−1`, (2.1), the coproduct (2.2) with twist `−1`
(the printed `√−1`-twist admits no coproduct; see [ERRATA.md](ERRATA.md)), coassociativity, `u⁺ ↪ U⁺`, and the comparison
with the [EKL] q-bialgebra at `q = √−1` (`EQQuantum.rU_mapDP`).

On skew polynomials (`Frontier.EQSkewDifferential`, `Frontier.EQOddDerivatives`; `OPol_n` with integer
coefficients, strands numbered from `0`, `ι` the parity involution, `θ(x_i) = (-1)^i x_i`, `w₀` the plain
permutation action):

- The local differential `d(x_i) = x_i²` on `OPol_n` with `d(fg) = d(f) g + ι(f) d(g)` and `d² = 0`:
  `EQSkewDifferential.d`, `d_mul`, `d_d`.
- Lemma 3.2: `d(e_k) = e_1 e_k - {k+1} e_{k+1}` for the untwisted odd elementary polynomials, and `d`
  preserves `OΛ_n`: `EQSkewDifferential.d_elementary`, `d_mem_osym` (the identity is proved for any family of
  anticommuting odd elements in a ring with an odd derivation, `D_strictSum`).
- Prop 3.1, left and right modules: `EQSkewDifferential.prop_3_1_left`, `prop_3_1_right`.
- Prop 3.7 / Def 3.8: the right action `1_z f = (θ ∘ w₀)(f) 1_z` on `Z_n = OPol_n(0,1,0,1,…)` is
  compatible with the differential, `EQSkewDifferential.dAlpha_mul_twistRev`. This is proved for all
  `f ∈ OPol_n`, not only `f ∈ OΛ_n`, from `d(φ f) = φ(d f) + s φ(f) - ι(φ f) s` (`d_twistRev`).
- Lemma 3.12 (odd partial derivatives form an exterior algebra; `d = Σ x_i² ∂/∂x_i`):
  `EQSkewDifferential.pd_pd`, `pd_pd_add`, `d_eq_sum`. Remark 3.13: `dAlpha_eq_sum_iff`.
  Lemma 3.14: `lemma_3_14`. Cor 3.15 (a null-homotopy of the identity of the complex `OPol_n(α)` when
  `α_i = 1`): `cor_3_15`, `acyclic`.
- Untwisted and twisted odd Schur polynomials (3.24)–(3.25) (`Frontier.EQSchur*`): `EQSchur.untwisted`,
  `EQSchur.twisted`; (3.27) `twisted_eq_theta_untwisted`; the SZ relations (3.28) `sz_relation_left`,
  `sz_relation_right`; Remark 3.10 (the twisted ones are EKL's odd Schur polynomials) `twisted_eq_schurAll`.
- Prop 3.11 (`d(s_λ)`, every rank): `EQSchur.prop_3_11`, with the all-exponent form `d_untwisted`. On `Z_n`:
  `d(∂_i) = 1` (`EQSchur.dZ_divided_add`) and Lemma 3.5 acting on `Z_n` (`dZ_D_staircase`).
- The action of `ONH_n` on `Z_n` (`Frontier.EQZn*`, rank `N = n + 2` for `ONH`): `d(∂_i) = 1` on `Z_n`
  (`EQZn.dAlpha_divided_anticomm`), right `OΛ_n`-linearity of `∂_i` (`divided_mul_twistRev`), Cor 3.9
  (`ONH_n ≅ END_{OΛ_n^op}(Z_n)` as dg rings: `EQZn.onhEndEquiv`, `corollary_3_9`), Cor 3.6
  (`corollary_3_6`), Lemma 2.17 (1) and Lemma 2.18 (`staircase_mul`, `eqIdempotent_mul_polyElem`), Prop 3.7
  (`proposition_3_7`); (3.37) `dAlpha_zAlpha_monomial`, the basis `B'_n` with the corrected exponent range
  (see [ERRATA.md](ERRATA.md)) `zn_right_basis`, (3.38) `eq_3_38`, Prop 3.16 (1) (a finite filtration by
  `d`-stable right submodules with the cell differential) `prop_3_16_1`, Prop 3.16 (2) `dONH_acyclic`,
  Prop 3.17 (acyclicity of `Z_n` iff `n ≥ 2`) `prop_3_17_acyclic_iff`. Prop 3.17 as printed, with "cofibrant" the lifting
  property of §2.2 (`DG.HasLiftingProperty`): `EQCofib.prop_3_17`; for `n ≥ 2`, `Z_n` is not even K-projective
  (`EQCofib.ONH.zn_not_isKProjective`); ranks `0, 1` use `ONH_0 = OPol_0 ≅ ℤ`, `ONH_1 = OPol_1`.
- §4.1–§4.2 (`Frontier.EQThick*`, rank `n + 2`): the differential `e d(−)` of Lemma 2.2 on idempotent truncations
  (`EQThick.thickD`), the §4.2.1 displays (`eqIdempotent_mul_dONH`, `thickD_thick`), Prop 4.2 for splitters and mergers
  (`prop_4_2_splitter`, `prop_4_2_merger`, for all `a` and `b ≥ 1`), Cor 4.3 (`cor_4_3_split`, `cor_4_3_merge`), and the
  §4.1 displays: `e_n f e_n g e_n = e_n fg e_n` (`thick_mul_thick`), exploders (`exploder_composition`, `exploder_schur`),
  Remark 4.1 (`remark_4_1`), and, corrected (see [ERRATA.md](ERRATA.md)), `∂_{w_0} f = ± w_0(f) ∂_{w_0}` (`DElem_mul_poly`),
  the relation `e_n x_1⋯x_k e_n = (−1)^{binom(k,2)} ẽ_k e_n` (`convenient_relation`) and the slider relation (`slider`).
- §4.3 (`Frontier.EQZab*`; `Z_{a,b}` modelled on `OΛ_a ⊠ OΛ_b ⊆ OPol_{a+b}`): Def 4.6 (`EQZab.dZ_dZ`, `dZ_one`, `dT_right`,
  compatibility with the right action for all of `OPol_{a+b}`), the Pieri rule (4.23) (`pieri_twisted`), Lemma 4.7
  (`lemma_4_7_box_twisted`), Cor 4.8 (basis `zab_span_twisted`, `zab_indep_twisted`; a finite-cell filtration with
  `binom(a+b, a)` cells, `cor_4_8`), Cor 4.11 (the dual `Z^∨_{a,b}` is free of rank `binom(a+b,a)` with a cell-by-cell
  `d`-stable basis, `cor_4_11`), Lemma 4.5 corrected (see [ERRATA.md](ERRATA.md)), the displays after it: (4.18)
  (`hat_sz`) and, corrected, (4.19) (`hat_pieri_partition`) and (4.20) (`hat_d_partition`), the orthogonality (4.22) with
  the sign of EKL (4.35) (`pairing`), and Cor 4.10 (`cor_4_10`) for the trace `z^∨ = θ ∘ ∂_{a,b}` of (4.24), which is
  `w_0`-semilinear rather than linear (`trace_mul_twistRev`, `trace_not_linear`). Lemma 4.4 (`Frontier.EQBorelPresentation`):
  `γ : OH_{a,a+b} → (OΛ_a ⊠ OΛ_b)/M` is well defined and bijective for all `a, b` and `w_0`-semilinear rather than linear
  (`EQBorel.lemma_4_4`, `gamma_smul`, `lemma_4_4_printed_false`; see [ERRATA.md](ERRATA.md)). Prop 4.12 (1)
  (`Frontier.EQZabREnd`): `Hom_D(Z, Z⟦n⟧) ≅ Hⁿ(END(Z))` for `Z_{a,b}` and `Z_{a,b}^∨` (`prop_4_12_one`,
  `prop_4_12_one_dual`, from the generic `homShiftAddEquivOfIsKProjective`). Prop 4.13 (1) for every composition
  (`Frontier.EQZabBlocks`: basis `s̃_{λ_1}(X_1) ⋯ s̃_{λ_r}(X_r)` over `OΛ̃_n`, `EQBlocks.prop_4_13_one_span`,
  `prop_4_13_one_indep`, `card_Idx`). Prop 4.12 (2) in the form `END(Z_{a,b}) = Z_{a,b} ⊗ Z_{a,b}^∨`
  (`Frontier.EQZabEndRankOne`: every right-linear endomorphism is uniquely `Σ_μ f(s̃_μ(y) z) · δ_μ(−)`, a sum of the
  trace-pairing maps of the source, `EQFunctor.prop_4_12_two`, `prop_4_12_two_unique`; the source defines `E_{a,b}` only
  through these maps). Prop 4.13 (2) for every composition (`Frontier.EQZabBlocksDiff`: the
  `ℤ`-span of that basis is stable under the differential `dB a = τ ∘ d_α ∘ τ` of `Z_a`, `EQBlocks.prop_4_13_two`,
  with `d 1_z` as printed, `dB_one_cons`). Prop 4.13 (3) without gradings
  (`Frontier.EQZabBlocksHom`: right `OΛ̃_n`-linear maps `Z_a → Z_b` are `Idx a × Idx b` matrices over `OΛ̃_n`,
  `EQBlocks.prop_4_13_three`, from the basis `basisTBN`). Graded ranks (`Frontier.EQZabBlocksRank`): `grank HOM(Z_a, Z_b) =
  q^{D_b − D_a} [n; a]_q [n; b]_q` (`EQBlocks.grankHom_eq`), the printed value only when `D_a = D_b` (see
  [ERRATA.md](ERRATA.md)).
- Appendix A.1 (`Frontier.EQLima*`): hypercube complexes with arbitrary signs are contractible
  (`EQLima.hypercube_contractible`), Lemma A.1 (`lemma_A_1`), Lima partitions (`isLima_iff_printed`; no addable or
  removable white box iff Lima: `whiteSystem_crit_iff`), Prop A.2 (1) for any module with a partition basis on
  which `d` acts by (3.29) (`prop_A_2_one`), Prop A.2 (2) for `OΛ_N`, `N ≥ 2`, over `ℤ` (`prop_A_2_two'`,
  `cocycle_eq'`, `lima_independent'`; the untwisted odd Schur polynomials form a `ℤ`-basis of `OΛ_N`:
  `osymSchurBasis`); in every rank `N`: `prop_A_2_two_all`. The limit `OΛ` (the library's `Q`, twisted by `θ`) as a super dg
  ring with `d` compatible with the projections (`EQLima.DQ`, `piN_DQ`), Prop A.2 (1) for `OΛ` (`HQ_basis`), `H(OΛ)`
  commutative (`HQ.instCommRing`), and Prop A.3 for both generating sets (`prop_A_3_columns`, `prop_A_3_rows`); two claims
  in the printed proof are refuted (see [ERRATA.md](ERRATA.md)). The display before Prop A.3: `d(e_2²) = −2e_4e_1 + 2e_5`
  in `OΛ_N` and in `OΛ`, nonzero in `OΛ` (`d_elementary_two_sq`, `DQ_e_two_sq`, `DQ_e_two_sq_ne_zero`), and the
  characteristic 2 statement `H(Sym) = k[e_2², e_4², …]` (`EQPdg.cohomology_char_two`).
- Appendix A.2–A.3 (`Frontier.EQApp*`): the hypercube decomposition of any box system (`EQApp.decompEquiv_delta`); `U_n` as a
  direct sum of hypercube complexes with its initial vectors (`uDecompEquiv_dU`, `init_iff`), `H(U_n) = 0` for `n ≥ 2`, and
  `Z_n ≅ (⊕ Y_q) ⊗ OΛ_n` compatibly with `d` (`zDecompEquiv_d`); the cohomology of `V_{a,b}`: Lima basis for `a` even
  (`homologyVT_even`), zero for `a`, `b` odd, and a nonzero corrected basis for `a` odd, `b` even (`homologyVT_odd`; see
  [ERRATA.md](ERRATA.md)).
- Appendix A.4 (`Frontier.EQPdg*`; `n` variables over a field of characteristic `p`): slash cohomology and (A.4)
  (`EQPdg.slash_shiftV_pos`, `slash_shiftV_zero`); the `p`-differential `d(x_i) = x_i²` with `d^p = 0` (`pd_pow_char`), the
  formulas for `d(e_k)`, `d(h_k)` (corrected, see [ERRATA.md](ERRATA.md)) and `d(s_λ)` (`pd_schur`, Schur polynomials as
  bialternants); the theorem of A.4: `H_{/k}(Sym_n) = 0` for `k > 0` (`thmA4_1_pos`), `H_{/0}(Sym_n)` has basis the
  `p`-Lima Schur polynomials (`thmA4_1_zero`), and `k[e_p^p, e_{2p}^p, …] ↪ Sym_n` is a quasi-isomorphism (`thmA4_2`).
  The limit `Sym` (`EQPdg.SymLim`, the graded inverse limit along `x_{n+1} ↦ 0`, with `d` and `d^p = 0`, `dLim_pow_char`),
  (A.5)–(A.7) in `Sym` (`dLim_eLim`, `dLim_hLim`, `dLim_sLim`), and Theorem A.4 as printed, for `Sym`: `H_{/k}(Sym) = 0`
  for `k > 0` (`thmA4_1_pos_lim`), the `p`-Lima Schur functions form a basis of `H_{/0}(Sym)` (`thmA4_1_zero_lim`), and
  `k[e_p^p, e_{2p}^p, …] ↪ Sym` is a quasi-isomorphism onto a polynomial algebra (`thmA4_2_lim`, `evELim_injective`).
- Finite-cell filtrations in dg-lean form (`DG.FiniteCellFiltration`, from a generic triangular-basis criterion
  `DG.TriangularBasis.finiteCellFiltration`): `Z_n` over `OΛ_n` (Prop 3.16 (1), `EQFix.znFiniteCellFiltration`,
  `zn_isKProjective_osym`) and `Z_{a,b}` over `OΛ_{a+b}` with `binom(a+b,b)` cells (Cor 4.8, `EQFix.zabFiniteCellFiltration`,
  `zab_hasLiftingProperty`), and the dual bimodule `Z^∨_{a,b}` over `OΛ_{a+b}` (Cor 4.11, `EQFunctor.zdualFiniteCellFiltration`,
  `zdual_isKProjective`), built from dg-lean's graded dual `DG.RightDual A M = HOM_A(M, A)` of a right dg module
  (a dg `(A, B)`-bimodule for a dg `(B, A)`-bimodule `M`; the dual of a finite triangular right basis is a triangular
  left basis, `DG.RightBasis.dualTriangular`).
- **Conventions for Definitions 4.6 and 4.15** (one functor `I` and one functor `R`, used both in Theorem 4.17 and in
  Corollary 4.21). Ellis–Qi do not say how `OΛ_a ⊗ OΛ_b` acts on `Z_{a,b}` (Def 4.6) or how `OΛ_{a+b}` acts on `Z^♮_{a,b}`
  (Def 4.15). Here `g ∈ OΛ_{a,b}` acts on `Z_{a,b} = OΛ_a ⊠ OΛ_b · z` by left multiplication with `(w₀ × w₀)(g)`
  (`EQFunctor.Zab.instModuleAB`; in Ellis–Qi's model `OΛ̃_a ⊠ OΛ̃_b · z` this is the action through `θ ∘ w₀` on each
  factor), and `h ∈ OΛ_{a+b}` acts on `Z^♮_{a,b} = OΛ_{a,b}` by right multiplication with `h(y, x)` (the block swap
  `EQFunctor.swapOsym`). These are the actions for which the two halves of Corollary 4.21 hold
  ([ERRATA.md](ERRATA.md) [EQ] 23, 24). The `K₀` statements of Theorem 4.17 do not depend on the choice: they only use
  the left `OΛ_{a+b}`-module `Z^∨_{a,b}` and the regular module `R_{a,b}(OΛ_{a+b}) ≅ OΛ_{a,b}`.
  Comparison of the alternatives (`Frontier.EQActionCompare`, `Frontier.EQActionCompareRes`). For `Z^♮_{a,b}` the action is
  forced: for any morphism of dg rings `φ : OΛ_{a+b} → OΛ_a ⊗ OΛ_b` (`z^♮ h = φ(h) z^♮`), an isomorphism of dg bimodules
  `((Z_a ⊠ Z_b) ⊗ Z^♮_{a,b}) ⊗ Z^∨_{a+b} ≅ ONH^♮_{a+b}` implies `φ = h ↦ h(y, x)` (`EQFunctor.natAction_unique`, `a, b ≥ 2`);
  in particular the inclusion `h ↦ h(x, y)` fails (`no_resIso_incl`, `a = b = 2`, witness `e_2`). For `Z_{a,b}`, with
  `g ∈ OΛ_{a,b}` acting by `(w₀ × w₀)(T g)` for a permutation `T` of the variables, an isomorphism
  `(Z_a ⊠ Z_b) ⊗ Z_{a,b} ≅ ι^* Z_{a+b}` forces `(w₀ × w₀) T^{-1} (w₀ × w₀)` to fix `φ(OΛ_{a+b})` (`zabT_constraint`); for
  `a = b = 2` each of the seven non-identity elements of the group generated by `w₀ × 1`, `1 × w₀` and the block swap
  fails (`no_indEquiv_blockRev` — the plain action through `θ` in Ellis–Qi's model —, `no_indEquiv_xRev`,
  `no_indEquiv_yRev`, `no_indEquiv_swap`, `no_indEquiv_swap_blockRev`, `no_indEquiv_swap_xRev`, `no_indEquiv_swap_yRev`;
  witness `e_2`), while `T = id` (the action through `θ ∘ w₀` in Ellis–Qi's model) works (`indEquiv`). Sign twists of the
  variables are not dg (`parityInv_not_dg`), so they give no dg bimodule at all.
- §4.4, Definitions 4.14 and 4.15 on `ℤ`-graded derived categories (`Frontier.EQFunctor*`; `OΛ_a ⊗ OΛ_b` is the dg subring
  `EQFunctor.osymABDG a b` of `OPol_{a+b}`): the multiplication functor `I_{a,b} = Z^∨_{a,b} ⊗^L_{OΛ_a ⊗ OΛ_b} (−)`
  (`EQFunctor.mult`, via the derived tensor product with a dg bimodule over dg rings, `DG.DGBimodule.derivedTensor`) and the
  comultiplication functor `R_{a,b}`, derived induction along the block swap `OΛ_{a+b} → OΛ_a ⊗ OΛ_b`,
  `f(x, y) ↦ f(y, x)` (`EQFunctor.swapOsym`, `EQFunctor.comult`, left adjoint to
  restriction, `comultAdjunction`), both triangulated and preserving compact objects; `I_{a,b}(OΛ_a ⊗ OΛ_b) ≅ Z^∨_{a,b}`
  and `R_{a,b}(OΛ_{a+b}) ≅ OΛ_a ⊗ OΛ_b` (`multSelfIso`, `comultSelfIso`); on `K₀`,
  `[I_{a,b}(OΛ_a ⊗ OΛ_b)] = Σ_{μ ∈ Par(b,a)} (−1)^{|μ|} [OΛ_{a+b}]` and `[R_{a,b}(OΛ_{a+b})] = [OΛ_a ⊗ OΛ_b]`
  (`K0Mult_self`, `K0Comult_self`), the `ℤ`-graded form of the two computations in the proof of Thm 4.17. Def 4.18
  for `N ≥ 2` (`Frontier.EQFunctorEmbedding`): `J_N = Z_N^∨ ⊗^L_{ONH_N} (−) : D(ONH_N) → D(OΛ_N)` (`EQFunctor.J`, with
  `Z_N^∨` finite-cell over `OΛ_N`, `znDual_isKProjective`), fully faithful since `D(ONH_N) = 0` (Cor 4.19 for `N ≥ 2`,
  `jFullyFaithful`); for `N ≤ 1` (`Frontier.EQFunctorEmbeddingSmall`, `ONH_N = OPol_N`) `J_N` is an equivalence, since
  `Z_N^∨ ≅ OΛ_N` and `J_N ≅` derived induction along the isomorphism `OPol_N ≅ OΛ_N` (`jSmall_isEquivalence`,
  `jSmallFullyFaithful`; dg-lean's `DG.DGBimodule.derivedTensorIsoInduction`), so Cor 4.19 holds in every rank. The abelian and
  homotopy Morita equivalences (4.30)–(4.31) (`Frontier.EQFunctorEmbeddingAbelian`): `J^A_N : ONH_N-dmod ≌ OΛ_N-dmod`,
  `M ↦ Z_N^∨ ⊗_{ONH_N} M`, with quasi-inverse `Z_N ⊗_{OΛ_N} (-)` (`EQFunctor.JA`; `JASmall` for `N ≤ 1`), and
  `J^H_N : H(ONH_N) ≌ H(OΛ_N)` (`JH`, `JHSmall`), from the bimodule isomorphisms `Z_N ⊗_{OΛ_N} Z_N^∨ ≅ ONH_N` and
  `Z_N^∨ ⊗_{ONH_N} Z_N ≅ OΛ_N` (`Frontier.EQZnMorita`: `znTensorDualEquiv`, `znDualTensorEquiv`; from dg-lean's
  `DG.FullAction.mulEquiv`, `DG.FullAction.evEquiv` for a module with a finite right basis on which `E` acts
  faithfully by all right-linear endomorphisms) and dg-lean's Morita equivalence from invertible bimodules. On the
  components `ONH_a ⊗ ONH_b` (`a, b ≥ 2`, `Frontier.EQFunctorEmbeddingTensor`): `J^A`, `J^H` with
  `M ↦ (Z_a^∨ ⊠ Z_b^∨) ⊗_{ONH_a ⊗ ONH_b} M` (`EQFunctor.JA2`, `JH2`), from dg-lean's external tensor product of
  dg bimodules and its interchange isomorphism. The bimodule behind the induction half of Cor 4.21
  (`Frontier.EQInductionBimodule`, ranks `a, b ≥ 2`): `(Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z_{a,b} ≅ ι^* Z_{a+b}` as dg
  `(ONH_a ⊗ ONH_b, OΛ_{a+b})`-bimodules, `y ⊗ F ↦ y (θ_a ⊗ θ_b)(F)` (`EQFunctor.indEquiv`), for `Z_{a,b}` with
  `OΛ_a ⊗ OΛ_b` acting through `θ ∘ w₀` on each factor (`EQFunctor.ZabTw`); for the action through `θ_a ⊗ θ_b`
  no such isomorphism exists (`EQFunctor.no_indEquiv_untwisted`, `a = b = 2`; ERRATA [EQ] 23). With it, the induction
  half of Cor 4.21 (`Frontier.EQInductionFunctor`): `J^A ∘ Ind ≅ I ∘ J^A` on abelian categories (`EQFunctor.indIsoA`,
  `Ind` = extension of scalars along `ι`, `I = Z_{a,b}^∨ ⊗ (-)`), on homotopy categories (`indIsoH`) and on derived
  categories (`indIsoD`; `D(ONH_a ⊗ ONH_b) = 0`, `onhTensor_isZero_derivedCategory`), from the adjunctions `Ind ⊣ Res`
  and `Z_{a,b}^∨ ⊗ (-) ⊣ Z_{a,b} ⊗ (-)` (dg-lean's `DG.RightBasis.dualAdjunction`, for a
  bimodule with a finite right basis). The restriction half of Cor 4.21 (`Frontier.EQRestrictionFunctor`, ranks
  `a, b ≥ 2`): `ONH^♮_{a+b}` of (4.32) as the right ideal `P^a ONH_{a+b}`, `P = x_{a+1} ⋯ x_{a+b}`, regraded so that
  `1^♮ = P^a` has degree `0` (`Frontier.EQOnhNat`: `EQFunctor.ONHNat`; it is stable under left multiplication by
  `ι(ONH_a ⊗ ONH_b)`, `iota_mul_Pw`, and `d(P^a) = {a} e_1(y) P^a`, `d_Pw`; ERRATA [EQ] 24; regrading by dg-lean's
  `DG.Regrade`), `Z^♮_{a,b}` of Def 4.15 with `OΛ_{a+b}` acting through the block swap
  `swapDG : OΛ_{a+b} → OΛ_a ⊗ OΛ_b`, `f(x, y) ↦ f(y, x)` (`EQFunctor.ZNat`), the bimodule isomorphism
  `((Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z^♮_{a,b}) ⊗_{OΛ_{a+b}} Z_{a+b}^∨ ≅ ONH^♮_{a+b}` (`gEquiv`, `gEquiv_op_smul`), and
  `R ∘ J^A ≅ J^A ∘ Res^♮` on abelian categories (`resIsoA`; `Res^♮ = ONH^♮ ⊗ (-)`, `R = Z^♮_{a,b} ⊗ (-)`), on
  homotopy categories (`resIsoH`) and on derived categories (`resIsoD`, for every functor `D(ONH_{a+b}) → D(ONH_a ⊗ ONH_b)`,
  both categories being zero). Definition 4.20 on derived categories (`Frontier.EQRestrictionDerived`):
  `Res^♮ = ONH^♮ ⊗^L_{ONH_{a+b}} (-)` (`EQFunctor.ResNatD`, the derived tensor product with a dg bimodule), which needs
  `ONH^♮` to be K-projective as a left `ONH_a ⊗ ONH_b`-module; it is even contractible, by the homotopy
  `m ↦ (-1)^{|m|} m ∂_1` (a dg `(A, B)`-bimodule is contractible as a left `A`-module as soon as `d t = 1` for
  some `t ∈ B` of degree `-1`, dg-lean's `DG.isContractible_of_d_op_smul_eq_one`; `onhNat_isKProjective`), so no resolution is
  needed; with it `R ∘ J ≅ J ∘ Res^♮` (`resNatIsoD`).
  The induction half of Cor 4.21 in all ranks `a, b ≥ 0` (`Frontier.EQLiftInduction`, `EQLiftFunctor`, `EQLiftAll`):
  `ONH_N = EQK0Int.ONHAll N` (`OPol_N` for `N ≤ 1`) acts fully on `Z_N` for every `N` (`EQLift.fullActionAll`); the
  bijection `Ψ : (Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z_{a,b} → Z_{a+b}`, `y ⊗ F ↦ y (θ_a ⊗ θ_b)(F)` (`gIndHom`), is compatible
  with gradings, differentials and the right `OΛ_{a+b}`-actions in every rank, and transporting the left action along
  it defines `ι_{a,b} : ONH_a ⊗ ONH_b → ONH_{a+b}` (`EQLift.iotaAll`, a morphism of dg rings acting on
  `Z_{a+b} = Z_a ⊠ Z_b` factorwise, `iotaAll_smul_polyHom`; for `a, b ≥ 2` it is `ONH.iota`, `iotaAll_eq_iota`).
  Generic for full actions (`EQLift.indIsoAg`, `indIsoHg`); for `ONH`: `J^A ∘ Ind ≅ I ∘ J^A` and `J^H ∘ Ind ≅ I ∘ J^H`
  for all `a`, `b` (`EQLift.indIsoAll`, `indIsoHAll`).
  The restriction half in all ranks (`Frontier.EQLiftRestrictionPoly`, `EQLiftRestriction`, `EQLiftResFunctor`): the
  polynomial identities for `P^a` (`PAG_mul`, `dAlpha_PAG`, `tau_blockRev_swapG`) in every rank; for full actions,
  `P^a ∈ E_{a+b}` (`PwG`; for `a, b ≥ 2` it is `Pw`, `PwG_eq_Pw`), `ONH^♮` as the right ideal `P^a E_{a+b}` regraded
  (`ONHNatG`; stability under `ι(E_a ⊗ E_b)` comes from the bimodule map, no sign twist needed), the bimodule
  isomorphism `((Z_a ⊠ Z_b) ⊗ Z^♮_{a,b}) ⊗ Z^∨_{a+b} ≅ ONH^♮_{a+b}` (`gEquivG`) and `R ∘ J^A ≅ J^A ∘ Res^♮`,
  `R ∘ J^H ≅ J^H ∘ Res^♮` (`resIsoAg`, `resIsoHg`); for `ONH`, all `a`, `b`: `EQLift.resIsoAll`, `resIsoHAll`.
  Derived categories in all ranks (`Frontier.EQLiftDerived`): the functors `J`, `J_2`, `Ind`, `I`, `R` for all `a`, `b`
  (`JDAll`, `J2DAll`, `IndDAll`, `IDAll`, `RDAll`); `D(ONH_N) = 0` for `N ≥ 2` and `D(ONH_a ⊗ ONH_b) = 0` for `a ≥ 2` or
  `b ≥ 2`; for `a + b ≥ 2`, `ONH^♮_{a+b}` is contractible, hence K-projective, over `ONH_a ⊗ ONH_b` and
  `Res^♮ = ONH^♮ ⊗^L (-)` (`ResNatDAll`), with `R ∘ J ≅ J ∘ Res^♮` (`resNatIsoDAll`); the induction half for `a ≥ 2`
  or `b ≥ 2` (`indIsoDAll_of_two`). Derived induction along a composite of dg ring maps (dg-lean's `DG.DGRingHom.derivedInductionCompIso`).
  For `(a, b) = (1, 1)`, where `D(ONH_1 ⊗ ONH_1) ≠ 0` (`Frontier.EQLiftOneOne`): `Z_{1,1} ≅ Z_2` as right dg
  `OΛ_2`-modules, so `Z_{1,1}^∨ ≅ Z_2^∨` is acyclic (`∂_1` acts on `Z_2^∨` on the right with `d ∂_1 = 1`) and
  `I_{1,1} = Z_{1,1}^∨ ⊗^L (-)` vanishes (the derived tensor product with a
  K-projective acyclic bimodule is zero, dg-lean's `DG.DGBimodule.derivedTensor_isZero_obj`), giving `J ∘ Ind ≅ I ∘ J`
  (`indIsoDOneOne`). For `a + b ≤ 1` (`Frontier.EQLiftSmallRank`, `EQLiftSmallDerived`): any dg ring `E` acting on
  `Z_N`, `N ≤ 1`, acts through a morphism `χ : E → OΛ_N`, `e 1_z = 1_z χ(e)` (`chiE`, bijective for full actions),
  every bimodule involved is a ring through a dg ring map (`Z_{a,b}^∨ ≅ OΛ_{a+b}` through `ψ(f ⊗ g) = f(x) g(y)`,
  `zabDualEquivSmall`; `Z_a^∨ ⊠ Z_b^∨ ≅ OΛ_a ⊗ OΛ_b` through `χ_a ⊗ χ_b`, `zzDualEquivSmall`), `ι` is bijective
  (`gIota_bijective`), `P^a = 1` and `ONH^♮` is free of rank one (`natDGEquivSmall`), so every functor is a derived
  induction; `χ ∘ ι = ψ ∘ (χ_a ⊗ χ_b)` (`chiE_comp_gIota`) and `swap ∘ χ = (χ_a ⊗ χ_b) ∘ ι^{-1}`
  (`swapDGG_comp_chiE`) give `J ∘ Ind ≅ I ∘ J` and `R ∘ J ≅ J ∘ Res^♮` (`indIsoDAllSmall`, `resNatIsoDAllSmall`).
  **Both halves of Cor 4.21 on derived categories, all `a`, `b`**: `EQLift.indIsoDAny`, `resNatIsoDAny`, with
  `Res^♮ = ONH^♮ ⊗^L (-)` in every rank (`ResNatDAllAny`; `ONH^♮` is K-projective over `ONH_a ⊗ ONH_b` in every rank,
  `onhNatAll_isKProjective_all`); the auxiliary `CatModule.HasDerivedCategory` instances are taken at universe `0`,
  as `DG.DGBimodule.derivedTensorIsoInduction` requires. The `⊠` form of
  Def 4.14 (`Frontier.EQFunctorBox`): `I_{a,b}(M, N) = Z^∨_{a,b} ⊗^L_{OΛ_{a,b}} (M ⊠ N)` with dg-lean's derived external
  tensor product transported along `OΛ_a ⊗ OΛ_b ≅ OΛ_{a,b}` (`EQFunctor.multBox`), `I_{a,b}(OΛ_a, OΛ_b) ≅ Z^∨_{a,b}`
  (`multBoxSelfIso`), and its symbol `[M] ⊗ [N] ↦ [I_{a,b}(M, N)]` with
  `[I_{a,b}(OΛ_a, OΛ_b)] = Σ_{μ ∈ Par(b,a)} (-1)^{|μ|} [OΛ_{a+b}]` (`K0MultBox_mk`, `K0MultBox_self`).
- §4.4 on half-graded modules (`Frontier.EQHalfGradedLift`, over `ℤ`), the setting of Theorems 3.18, 4.17 and
  Lemma 4.16: the functors of Definitions 4.14, 4.15, 4.18, 4.20 and (3.40) as derived tensor products with the diagonally
  regraded bimodules over the weight dg categories (dg-lean's `DG.Diagonal.derivedTensor`): `EQLift.JH`, `J2H`, `IH`,
  `RH`, `IndH`, `ResNatH` (for `R` and `Ind` the bimodule is the ring through the dg ring map, dg-lean's
  `DG.DGRingHom.Bimodule`). Each is the diagonal transport of the `ℤ`-graded functor (`jHTransportIso`, `iHTransportIso`,
  `rHTransportIso`, `indHTransportIso`, `resNatHTransportIso`; dg-lean's `DG.Diagonal.derivedTensorTransportIso`), and
  transport is functorial (dg-lean's `DG.Diagonal.transportCompIso`, `transportMapIso`), so **Corollary 4.21 holds on
  half-graded derived categories** in all ranks (`EQLift.indIsoH`, `resIsoH`), and **Corollary 4.19**: `J` is fully
  faithful on half-graded derived categories in every rank (`jHFullyFaithful`; for `N ≥ 2` the half-graded derived
  category of a dg ring with `d t = 1`, `t` of degree `-1`, is zero, `isZero_halfGraded_of_d_eq_one`; for `N ≤ 1`,
  `J ≅ χ^*` is a triangulated equivalence and the transport of an equivalence is one,
  `transportFullyFaithfulOfIsEquivalence`). The `ℤ`-graded statements above are the restrictions along the diagonal
  functors. **Corollary 4.19 on `K₀`** (`Frontier.EQCor419K0`): the symbol `[J] : K₀(D(ONH)) → K₀(D(OΛ))` of the
  half-graded `J` (`EQK0.jK0Int` over `ℤ`, `EQK0.jK0` over a field; `[J_N]` is the identity under `K₀ ≅ ℤ[√−1]` for
  `N ≤ 1`, since `Z_N^∨ ≅ OΛ_N`) is, under the isomorphisms of Theorems 3.18 and 4.17, the inclusion `ι : u⁺ ↪ U⁺`,
  `E ↦ E^{(1)}` (`cor_4_19_int_K0`, `cor_4_19_K0`); hence it is injective and a map of twisted bialgebras
  (`cor_4_19_int_mul`, `cor_4_19_int_comul`; `cor_4_19_mul`, `cor_4_19_comul`).
- `OΛ_{a,b} = OΛ_a ⊗ OΛ_b` (`Frontier.EQFunctorRingTensor`): `f ⊗ g ↦ f(x) g(y)` is an isomorphism of dg rings from
  dg-lean's graded tensor product (Koszul sign rule) onto `EQFunctor.osymABDG a b` (`EQFunctor.tensorToOsymAB`,
  `tensorToOsymAB_bijective`, `tensorEquivOsymAB`), from the block supercommutation `g(y) u(x) = (-1)^{ij} u(x) g(y)`
  (`inclY_mul_inclX_of_mem`).
- §4.4 and §3.6 Grothendieck groups over a field `K` (`Frontier.EQK0*`), in the half-graded setting of §2.2.4: the dg
  rings are base changed to `K` (dg-lean's `ExtendScalars K`) and given the diagonal half-grading (degree `k` in
  bidegree `(2k, k mod 2)`); `K₀` is the compact super Grothendieck group (classes up to isomorphisms of either parity),
  a `ℤ[√−1]`-module with `√−1` acting by the internal shift `⟨1⟩`. For every dg ring connected over `ℤ`
  (`EQK0.IsConnectedInt`: zero in negative degrees, `ℤ · 1` in degree `0`), `K₀ ≅ ℤ[√−1]` with the regular class `1`
  (`EQK0.superK0GaussianOfConnected`); this applies to `OPol_n` and its dg subrings (`isConnectedInt_dgSubring`), giving
  `K₀(D(OΛ_a)) ≅ ℤ[√−1]` (`superK0OsymEquiv`), the same for `OΛ_{a,b}` and for `ONH_n = OPol_n`, `n ≤ 1`
  (`superK0OPolEquiv`), and `K₀(D(ONH_{n+2})) = 0` (`superK0c_onh_subsingleton`); Lemma 4.16 with
  `[OΛ_a] ⊗ [OΛ_b] ↦ [OΛ_{a,b}]` (`lemma_4_16`, `lemma_4_16_tmul_self`). The comultiplication of Thm 4.17
  (`Frontier.EQK0Coproduct`): `R_{a,b}` on half-graded modules is derived induction along the morphism of half-graded
  dg rings induced by `K ⊗ swapOsym` (`EQK0.extendSwapDG`); its symbol followed by Lemma 4.16 sends
  `E^{(a+b)} = [OΛ_{a+b}⟨-binom(a+b,2)⟩]` to `(-√−1)^{ab} E^{(a)} ⊗ E^{(b)}` (`EQK0.comultK0_ePowClass`), the
  `(a, b)`-term of (2.2) with the twist `−1` of [ERRATA.md](ERRATA.md) [EQ] 1. The multiplication of Thm 4.17
  (`Frontier.EQK0Mult`): over `K`, `I_{a,b} = (K ⊗ Z^∨_{a,b}) ⊗^L (-)` (`EQK0.multK`, dg-lean's base change of dg
  bimodules), with `[I_{a,b}(K ⊗ OΛ_{a,b})] = Σ_μ (-1)^{|μ|} [K ⊗ OΛ_{a+b}]` (`K0MultK_self`); on half-graded modules it
  is `(K ⊗ Z^∨_{a,b})ᵈ ⊗^L (-)`, the derived tensor product with the diagonally regraded bimodule (`multKHalf`,
  dg-lean's `Diagonal.derivedTensor`), which is the diagonal transport of `I_{a,b}` (`multKHalfTransportIso`: it acts
  by `I_{a,b}` on the four weight blocks and commutes with the internal shift) and extends `I_{a,b}` along the
  diagonal functors (`multKHalfToDerivedIso`).
  Its symbol composed with Lemma 4.16 gives (2.1), `E^{(a)} E^{(b)} = [a+b, a]_{√−1} E^{(a+b)}` (`EQK0.multK0_ePowClass`).
  **Thm 4.17** (`Frontier.EQThm417`, over a field `K`, with the conventions above): `U⁺ ≅ ⨁_n K₀(D(OΛ_n))` as
  `ℤ[√−1]`-modules, `E^{(n)} ↦ [OΛ_n⟨-binom(n,2)⟩]` (`EQK0.thm_4_17_equiv`), intertwining the product of `U⁺` with
  the multiplication `[I]` (Lemma 4.16 followed by the symbols of `I_{a,b}`; `thm_4_17_mul`) and the coproduct (2.2)
  for the twist `−1` with the comultiplication `[R]` (symbols of `R_{a,b}` followed by Lemma 4.16; `thm_4_17_comul`);
  so `K₀(D(OΛ))` with `[I]`, `[R]` is a twisted bialgebra isomorphic to `U⁺` (the algebra bookkeeping is
  `Frontier.EQK0Assembly`). **Thm 3.18** (`Frontier.EQThm318`, same conventions): `ONH_0 = OPol_0`, `ONH_1 = OPol_1`
  have `K₀ ≅ ℤ[√−1]` and `K₀(D(ONH_n)) = 0` for `n ≥ 2`; with `ι_{m,n}` the dg ring isomorphism
  `OPol_m ⊗ OPol_n ≅ OPol_{m+n}` (`EQFunctor.opolTensorDG`, `opolTensorEquiv`; followed by `OPol_2 ⊆ ONH_2` for
  `ι_{1,1}`; for `m, n ≥ 2`, `ι_{m,n} : ONH_m ⊗ ONH_n → ONH_{m+n}` is the strand-window morphism of dg rings
  `EQOnhDG.ONH.iota`, `Frontier.EQOnhTensor`) and the Künneth isomorphism (3.44) (`EQK0.kunneth`), the symbols of
  `Ind_{m,n}` and `Res_{m,n}` give the
  structure constants of `u⁺`: `1·1 = 1`, `1·E = E·1 = E`, `E·E = 0`, `r(1) = 1 ⊗ 1`, `r(E) = E ⊗ 1 + 1 ⊗ E`
  (`thm_3_18_mul_one_one`, `thm_3_18_mul_one_E`, `thm_3_18_mul_E_one`, `thm_3_18_mul_E_E`, `thm_3_18_comul_one`,
  `thm_3_18_comul_E_left`, `thm_3_18_comul_E_right`); all other components have source or target `0`. `Res_{m,n}`
  for `m + n ≤ 1` is computed as derived induction along `ι_{m,n}^{-1}`. **Thm 3.18 over `ℤ`**
  (`Frontier.EQThm318Int`, the integral dg rings themselves): the unit `ℤ → OPol_N` is a quasi-isomorphism for
  `N ≤ 1` (`EQK0.intUnit_opol_isQuasiIso`, from `H(OPol_N) = ℤ · 1`, `Frontier.EQSmallRankDG`), so
  `K₀(D(OPol_N)^c) ≅ K₀(D(ℤ)^c) ≅ ℤ` (dg-lean's quasi-isomorphism invariance of `K₀` and `K₀(ℤ) ≅ ℤ`;
  `EQK0.baseK0OPolInt`) and `K₀(D(ONH_N)) ≅ ℤ[√−1]` (`superK0OPolIntEquiv`); `K₀(D(ONH_n)) = 0` for `n ≥ 2`
  (`superK0c_onh_int_eq_zero`); with the Künneth isomorphism (3.44) for `m + n ≤ 1` (`kunnethInt`) the same
  structure constants hold (`thm_3_18_int_*`). For `E · E` the Künneth map `[ONH_1] ⊗ [ONH_1] ↦ [ONH_1 ⊗ ONH_1]`
  (`kunnethMapInt`) suffices, since the product lands in `K₀(D(ONH_2)) = 0`; it is in fact the Künneth
  isomorphism over `ℤ` (`Frontier.EQKunnethInt`: `OPol_1 ⊗ OPol_1` has `Z¹ = 0` and torsion-free `H²`, so
  `K₀(D(OPol_1 ⊗ OPol_1)^c) ≅ ℤ`; `EQK0Int.kunnethOneOneInt`, `kunnethMapInt_one_one_eq`). **The Künneth
  isomorphism (3.44) holds over `ℤ` for all `m, n`** (`Frontier.EQKunnethIntAll`, `EQK0Int.kunnethIntAll`,
  `[ONH_m] ⊗ [ONH_n] ↦ [ONH_m ⊗ ONH_n]` by `kunnethIntAll_reg`, with `ONH_N` = `EQK0Int.ONHAll N` for every
  `N` and `ONH_m ⊗ ONH_n` dg-lean's graded tensor product over `ℤ`): for `m ≥ 2` or `n ≥ 2` the dg ring
  `ONH_m ⊗ ONH_n` is acyclic (`d (∂₁ ⊗ 1) = 1`, resp. `d (1 ⊗ ∂₁) = 1`), so both sides vanish.
- Ground ring of §4.4 (footnote 5 asserts that the results hold over `ℤ`, by formality and Thm 2.7). Status:
  **Thm 4.17 is proved over `ℤ`** (`Frontier.EQThm417Int`, the integral dg rings `OΛ_n`, `OΛ_{a,b}` themselves), by
  a different argument than the footnote's. The footnote's route has a gap: Corollary 2.6 (`K₀(A) ≅ K₀(A⁰)`) assumes
  `A⁰` semisimple, and formality replaces `OΛ_n` by its cohomology, which is again non-negatively graded with
  degree-`0` part `ℤ`. The only field-specific input of §4.4 is `K₀(D(OΛ_n)^c) ≅ ℤ`, `[OΛ_n] ↦ 1` (and the same for
  `OΛ_{a,b}`); over `ℤ` it follows from the low-degree cohomology (`Frontier.EQK0Int`): `OΛ_n` is concentrated in
  degrees `≥ 0` with degree-`0` part `ℤ · 1`, and by Prop A.2 (2) (Lima partitions have size divisible by `4`) every
  cocycle of degree `k ≢ 0 mod 4` is a coboundary (`EQK0Int.osym_eq_d_of_cocycle`), so `Z¹ = 0` and `H² = 0`;
  for `OΛ_{a,b} = OΛ_a ⊗ OΛ_b`, `Z¹ = 0` and `H²` is torsion-free (`osymAB_cocycle_one`,
  `osymAB_cohomology_two_torsionFree`, from dg-lean's `DG.ConnectedTensor`). dg-lean's
  `DG.DGRing.K0.equivIntOfIsConnectedInt` then gives `K₀ ≃ ℤ`, `[A] ↦ 1` (every compact object of `D(A)` has a tower
  of shifts of finitely generated abelian groups, `DG.Derived.ConnectedK0`, `DG.Derived.IntegralHeart`), which is
  `EQK0Int.baseK0OsymInt`, `baseK0OsymABInt`. The rest of §4.4 is unchanged: `superK0OsymIntEquiv`
  (`K₀(D(OΛ_n)) ≅ ℤ[√−1]`), `lemma_4_16_int`, `comultK0Int_ePowClass`, `multK0Int_ePowClass` (the multiplication
  functor is `(Z^∨_{a,b})ᵈ ⊗^L (-)` on half-graded modules), and `thm_4_17_int_equiv`, `thm_4_17_int_mul`,
  `thm_4_17_int_comul`, the same statements as over a field. Over every field all of §4.4 is proved as well (above).
- §2.2.4 over a field (`Frontier.EQHalfGradedField`): the compact super Grothendieck group of
  dg-lean's half-graded derived category is additively equivalent to the Gaussian integers
  (`EQHalfGraded.superK0EquivGaussian`), with the regular object representing `1` and its actual
  internal shift `⟨1⟩` representing `√-1` (`superK0EquivGaussian_shift_regular`). In contrast,
  `(1 + q²)[K] ≠ 0` in the ordinary even Grothendieck group (`even_super_relation_ne_zero`).
  `superK0GaussianLinearEquiv` upgrades the same comparison to a Gaussian-linear equivalence:
  scalar compatibility holds for every super class, and every integer internal shift of any
  compact object acts by the corresponding power of `i`. In particular, the regular object's
  negative unit shift represents `-i` (`superK0GaussianLinearEquiv_negShift_regular`).
  The comparison `⟨1⟩ ⋙ ⟨1⟩ ≅ ⟦1⟧ ⋙ Π` is an odd natural isomorphism
  (`internalShiftSquaredOddIso`); an even isomorphism between the twice-internally-shifted
  regular compact object and its translation is impossible (`no_even_shiftTwo_translation_regular`).
  This does not assert tensor-product multiplicativity or the case over `ℤ`; the nilHecke
  categorification theorems (Thm 3.18, Thm 4.17) are proved in `Frontier.EQThm318*` and
  `Frontier.EQThm417*` (above).
- The diagonal half-grading on the existing integral odd nilHecke dg ring (`Frontier.EQDiagonal`):
  `EQDiagonal.onh n` places `ONH_{n+2}`'s ordinary degree `k` at `(2k, k mod 2)`; its actual dots
  and crossings have bidegrees `(2,1)` and `(-2,1)`. The original differential is unchanged,
  including `d(xᵢ) = xᵢ²`, `d(∂ᵢ) = 1`, and bidegree `(2,1)`. This is a ring-level bridge,
  not by itself a derived module comparison or compact-generator result.
- For the entire half-graded module category of integral `ONH_{n+2}` (`Frontier.EQHalfGradedAcyclic`),
  the crossing contracts every weight, with no parity-versus-degree support restriction:
  `isAcyclic_halfGraded`, `isZero_halfGraded_derivedCategory`. Both ordinary and super Grothendieck
  groups of compact objects vanish (`compactK0_eq_zero`, `superK0c_eq_zero`). These statements cover
  ranks at least two only; the integral half-graded compact Grothendieck groups in ranks zero
  and one and the Künneth isomorphism are computed in `Frontier.EQThm318Int` and
  `Frontier.EQKunnethIntAll` (above).
- Integral ordinary dg cohomology in ranks zero and one (`Frontier.EQSmallRankDG`): for the
  actual `OPol_N` dg ring with `N ≤ 1`, `cohomologyZeroEquivInt` identifies `H⁰` with `ℤ`,
  taking the actual constant class to its integer, and `cohomology_eq_zero_of_ne_zero` proves
  vanishing in every nonzero cohomological degree. The existing Lima theorem supplies a
  boundary-plus-constant normal form with a unique integral constant; homogeneous projection
  supplies genuine graded boundaries. `Frontier.EQSmallRankQuasiIso` proves the actual unit
  inclusion `ℤ → OPol_N` is a dg-ring quasi-isomorphism (`intInclusion_isQuasiIso`). Keller's
  theorem gives the ordinary derived equivalence and the ordinary compact `K₀` equivalence
  (`derivedEquivalence`, `compactK0Equiv`), taking the regular integral class to the regular
  polynomial class (`compactK0Equiv_self`). This does not compute `K₀(ℤ)` numerically or supply
  the half-graded derived equivalence, half-graded compact `K₀` calculation, or tensor formula.
- `Frontier.EQHalfGradedUnit` constructs the actual integral unit dg functor on the weight
  categories of the diagonal half-gradings, in every rank. It maps placed integer components
  to the corresponding polynomial components, preserving multiplication, differential,
  cohomological degree, weight, and both periodicity units.
- `Frontier.EQHalfGradedUnitQuasiEquivalence` proves that this actual unit functor is a dg
  quasi-equivalence for ranks zero and one. Its Hom-cohomology map is bijective in every
  degree and between arbitrary weights: homogeneous ordinary representatives and actual
  primitives are placed at the appropriate half-graded indices, and unsupported coefficients
  vanish. Identity cocycles witness essential surjectivity on weight objects.
- `Frontier.EQHalfGradedUnitDerived` applies Keller's theorem to this same functor, giving
  derived induction/restriction as an equivalence on all half-graded modules in ranks zero
  and one, not only diagonal modules. The forward functor commutes with cohomological shift
  and preserves distinguished triangles. Its equivalence of ordinary compact `K₀` groups
  sends each weight representable to the representable at that same weight. The numerical
  compact `K₀` and the Künneth isomorphism are in `Frontier.EQThm318Int`, `Frontier.EQKunnethIntAll`; the
  super-`K₀` comparison is below.
- `Frontier.EQHalfGradedUnitParity` proves that actual derived restriction along the unit
  commutes with every internal shift and the existing parity shift in every rank. In ranks
  zero and one, the unit and counit of Keller's equivalence give these comparisons for
  actual derived induction as well. Neither shift is defined by transport. Restriction
  to compact objects and descent to super-`K₀` are supplied by the next module;
  these natural isomorphisms do not assert parity-involution coherence or a numerical formula.
- `Frontier.EQHalfGradedUnitSuperK0` restricts the actual internal-shift and parity
  comparisons to compact objects for `N ≤ 1`. The original `compactK0Equiv` maps the
  actual parity-relation subgroup onto its target counterpart, giving `superK0cEquiv`
  between the existing compact super Grothendieck groups. Every compact object class
  maps to its actual perfect induction. No replacement quotient or transported shift
  is used. (Numerical calculations and the Künneth isomorphism: `Frontier.EQThm318Int`,
  `Frontier.EQKunnethIntAll`.)
- `Frontier.EQHalfGradedUnitParityCoherence` proves, in every rank, that actual module
  restriction along the integral unit respects both existing parity involutions.
  The proof uses preservation of the inverse periodic unit, and gives the complete
  natural-isomorphism square and its image under the actual localization functor `Q`.
  Module and source-localization universes remain independent. The separate modules
  below identify the derived comparison and prove its involution coherence, under
  that original comparison's source-universe constraint. Low-rank induction
  parity-involution coherence is supplied by the induction module below.
- `Frontier.EQHalfGradedRestrictionCoherence` computes the existing derived
  restriction-composition isomorphism on actual localized modules, using the original
  module comparison. It also proves coherent-shift compatibility of the existing
  module-localization restriction comparison. The consumer checks both compositions
  of the integral unit with actual weight translations, in every rank and with
  independent source/target localization universes.
- `Frontier.EQHalfGradedUnitDerivedParityCoherence` identifies the existing
  `restrictParityIso` on localized modules with the actual module parity comparison
  through the original localization isomorphisms, in every rank. It retains the
  original equality of source Hom and module universes, with independent target
  Hom universe. It also computes the original `parityShiftDIso` on localized modules
  with independent module/derived Hom universes.
- `Frontier.EQHalfGradedUnitDerivedParityInvolution` pastes those formulas with the
  actual module involution square and descends by the localization universal property.
  The original `restrictParityIso` consequently intertwines the original derived
  `parityShiftDIso` involutions on every derived target object, in every rank. Both
  the full natural-isomorphism square and its component formula are proved. The
  source derived Hom universe equals the module universe, as in the original
  comparison; the target Hom universe is independent. No comparison or involution
  is replaced.
- `Frontier.EQHalfGradedUnitInductionParityInvolution` proves the componentwise and
  full natural-isomorphism involution squares for actual derived induction when
  `N ≤ 1`, using the original `derivedEquivalenceParityIso` and both original
  `parityShiftDIso` involutions. Its unit mate identity is proved from the existing
  equivalence unit/counit, not assumed; restriction faithfulness and the published
  restriction square then give induction coherence on every source derived object.
  The source derived Hom universe remains the module universe and the target Hom
  universe is independent. No all-rank induction equivalence is asserted
  (numerical calculations and the Künneth isomorphism: `Frontier.EQThm318Int`, `Frontier.EQKunnethIntAll`).
- Scope of the nilHecke dg-lean statements: the dg rings and modules above are `ℤ`-graded by half the `q`-degree, so every
  homogeneous element has parity equal to its degree mod 2. The derived-category, cofibrancy and K-projectivity results
  for these constructions are statements about such modules. The new half-graded vanishing result
  extends Prop 3.16 (2) to parity-independent modules in ranks at least two. The broader cofibrancy
  and K-projectivity comparisons and the extension-of-scalars bridge are not supplied by it.
- dg structures (`Frontier.EQDGStructures`, on [dg-lean](https://github.com/apellis/dg-lean)); the `ℤ`-grading
  is half the `q`-degree (`x_i` in degree `1`), so the Koszul sign is the Ellis–Qi parity:
  `OPol_n` as a dg ring (`EQSkewDifferential.OPol.instDGRing`), `OΛ_n` as a dg subring (Lemma 3.2,
  `osymDG`), `OPol_n(α)` for `α ∈ {0,1}ⁿ` as a left dg module (Prop 3.1, `OPolAlpha.instDGModule`), and `Z_n`
  as a dg `(OPol_n, OPol_n)`-bimodule and, by restriction, a dg `(OPol_n, OΛ_n)`-bimodule (Prop 3.7, Def 3.8,
  `Zn.instDGBimodule`, `Zn.dgBimoduleOsym`).
- `ONH_n` (rank `n + 2`) as a dg ring (`Frontier.EQOnhDG*`): the half-`q`-degree grading
  (`EQOnhDG.grading`, compared with the library's `q`-grading in `grading_eq_degreePiece`), `EQOnhDG.ONH.instDGRing`,
  `d(x_j) = x_j²`, `d(∂_i) = 1` (`ONH.d_x`, `ONH.d_del`), the dg inclusion of `OPol_{n+2}` (`ONH.polyHom`), Prop 3.16 (2)
  (`ONH.isAcyclic`, and every object of `D(ONH_n)` is zero: `ONH.isZero_derivedCategory`), `Z_n` as a dg
  `(ONH_n, OΛ_n)`-bimodule (`ONH.instDGBimoduleZn`), and Cor 3.9 as an isomorphism of dg algebras with dg-lean's
  endomorphism dg algebra (`ONH.toENDZnEquiv`; dg-lean's `END` acts on the right, so the statement is for the
  opposite of `ONH_n`).

#### [EQ]: coverage of the numbered statements

Every numbered statement of [EQ] (§§2–4 and Appendix A; theorem-like environments and the numbered displays that
make a claim; displays that only fix notation are grouped with the statement they belong to), with the modules where
it is formalized. Modules are under `OddMath.` unless marked dg-lean (under `DG`, generic). "[EQ] n" refers to
[ERRATA.md](ERRATA.md). The `ℤ`-grading of the dg rings is half the `q`-degree (see the scope note above); `K₀` is the
compact super Grothendieck group of half-graded modules (§2.2.4).

| Statement | Subject | Modules | Status |
|---|---|---|---|
| (2.1), (2.2) | divided-power product and coproduct of `U⁺` at `q = √−1` | `Frontier.EQQuantumGroups`, `Frontier.EQQuantumBinomial`, `Frontier.EQQuantumBialgebra` | formalized with the twist `−1` ([EQ] 1, 2) |
| (2.3)–(2.5) | super Leibniz rule for dg algebras and dg modules | dg-lean `Algebra`, `Module`; `Diagrams.OddNilHecke.Differential` | definitions; (2.3) on `ONH_n`: `d_mul_of_mem` |
| Remark 2.1 | dg categories | dg-lean `Category` | remark; not a target (dg-category versions of §2.2 are in dg-lean) |
| (2.6)–(2.8) | `END_A(M)`, its differential, the right action of `END_A(M)` | dg-lean `Module.End` | definitions, formalized |
| (2.9), Lemma 2.2 | `HOM_A(Ae, Ae) ≅ eAe`; `Ae` over `(eAe, d_e)` when `d e ∈ Ae` | dg-lean `Module.CornerEnd` (`LeftDGIdempotent`, `endLeftCornerEquiv`) | formalized |
| (2.10) | `Hom_{H(A)}(M, N) = H⁰(HOM_A(M, N))` | dg-lean `Homotopy.HomotopyCategory` | formalized |
| Proposition 2.3 | existence and uniqueness of cofibrant (K-projective) replacements | dg-lean `Category.Resolution` (`exists_kProjective_resolution`, `SemiFreeResolution.dgHomotopyEquiv`) | formalized |
| (2.11), (2.12) | morphisms in `D(A)` through a resolution; `RHOM` | dg-lean `Derived.ConnectedK0` (`homShiftAddEquivOfIsKProjective`), `Category.Derived.Tensor` (`rhom`) | formalized |
| Example 2.4 | finite-cell modules are compact | dg-lean `Category.Derived.FiniteCell` | formalized |
| Theorem 2.5 | Schnürer: compact iff finite-cell, for positive dg algebras | dg-lean `Positive.Schnurer` (`IsPositive.isCompact_iff`) | formalized (no field hypothesis) |
| Corollary 2.6 | `K₀(A) ≅ K₀(A⁰)` for positive `A` | dg-lean `Positive.K0Basis`, `HalfGraded.Positive` (`IsPositive.K0DegreeZeroEquiv`) | formalized |
| (2.13)–(2.16) | derived tensor and hom functors, their adjunction, induction and restriction | dg-lean `Category.Derived.Tensor`, `Category.Derived.DGBimodule`, `Category.Derived.TensorInduction` | formalized |
| Theorem 2.7 | a quasi-isomorphism of dg algebras induces an equivalence of derived categories | dg-lean `Category.Derived.Keller` (`DGRingHom.derivedEquivalence`) | formalized |
| Corollary 2.8 | `D(A) ≃ 0` iff `H(A) = 0` iff `d x = 1` for some `x` | dg-lean `Derived.Zero` (`DerivedCategory.tfae_isZero`) | formalized |
| (2.17) | `K₀(D(k)) ≅ ℤ[√−1]` | `Frontier.EQHalfGradedField` (fields), `Frontier.EQThm318Int` (`superK0OPolIntEquiv` with `OPol_0 = ℤ`) | formalized over every field and over `ℤ` |
| Remark 2.9 | homotopy versus derived category over `ℤ` | — | remark; not a target |
| Examples 2.10–2.12 | `k[S_n]`, `OPol_n`, KLR algebras as diagrammatic algebras | — | illustrations of the definition; not targets |
| Example 2.13, (2.18), (2.19) | the local differential on `OPol_n`; the twist `θ` | `Frontier.EQSkewDifferential` (`d`, `d_mul`, `d_d`, `theta`) | formalized |
| Remarks 2.14, 2.15 | EKL's odd elementary polynomials; `OΛ̃_n` is not `d`-stable | `Frontier.EQFixW0` (`theta_elementary`) | remarks (2.14 used and formalized; 2.15 not a target) |
| (2.20)–(2.22) | `w₀` on odd elementary polynomials; `θ ∘ w₀` versus `w₀ ∘ θ` | `Frontier.EQFixW0`, `Frontier.EQSchurDifferential` (`theta_longestPerm`) | formalized |
| (2.23), (2.24), Proposition 2.16, (2.25)–(2.31) | odd divided differences, `OΛ̃_n` as joint kernel and image, the relations of `ONH_n`, faithfulness ([EKL]) | `Frontier.LongestKernel`, `Frontier.LongestElementary`, `Frontier.NilHeckeBasis`, `Frontier.NilHeckeEndomorphism` | formalized (the [EKL] part) |
| (2.32)–(2.39) | diagrammatic relations of `ONH_n`; the words `∂_w`, `∂_{w₀}` | `Diagrams.OddNilHecke`, `Frontier.ZeroHecke`, `Frontier.LongestDivided` | formalized (definitions and comparison with `Presented n`) |
| Lemma 2.17, (2.40) | `x^δ`, `∂_{w₀}(x^δ)`, `∂_{w₀} f ∂_{w₀}`, the idempotent `e_n`, PBW bases | `Frontier.EQZnBimodule` (`staircase_mul`), `Frontier.LongestDivided` (`D_staircase`), `Frontier.OnhPolynomial` (`DElem_poly_DElem`), `Frontier.EQThickBlocks` (`eqIdempotent_mul_self`), `Frontier.NilHeckeBasis`, `Frontier.NilHeckeRightBasis` | formalized |
| Lemma 2.18, (2.41) | `e_n f = (θ ∘ w₀)(f) e_n` | `Frontier.EQZnBimodule` (`eqIdempotent_mul_polyElem`) | formalized (the identity cited in the proof needs a sign, [EQ] 6) |
| (3.1)–(3.3), Proposition 3.1 | `OPol_n(α)` is a left (right) dg module iff `α ∈ {0,1}ⁿ` | `Frontier.EQSkewDifferential` (`prop_3_1_left`, `prop_3_1_right`) | formalized |
| Lemma 3.2, (3.4), (3.5) | `d(e_k) = e_1 e_k − {k+1} e_{k+1}`; `d` preserves `OΛ_n` | `Frontier.EQSkewDifferential` (`d_elementary`, `d_mem_osym`) | formalized |
| (3.6)–(3.11), Proposition 3.3 | locality of the induced differential | `Frontier.EQFixProp33` (`prop_3_3`, `prop_3_3_iff`), `Diagrams.OddNilHecke.DifferentialAnsatz` | formalized (as printed, and an intrinsic variant) |
| (3.12) | display in the proof of Proposition 3.3 | — | proof step |
| Lemma 3.4, (3.13)–(3.15) | `d(∂_{w₀})` | `Diagrams.OddNilHecke.DifferentialLongest`, `…DifferentialLongestComparison` | formalized |
| Lemma 3.5, (3.16), (3.17) | `d(e_n)`, `d(x^δ)` | `Diagrams.OddNilHecke.DifferentialLongest`, `…DifferentialLongestComparison` | formalized |
| Corollary 3.6 | `ONH_n e_n ≅ OPol_n(0,1,0,1,…)` | `Frontier.EQZnAction` (`corollary_3_6`) | formalized |
| Proposition 3.7 | `OPol_n e_n` is a dg `(OPol_n, OΛ_n)`-bimodule | `Frontier.EQZnBimodule` (`proposition_3_7`), `Frontier.EQSkewDifferential` (`dAlpha_mul_twistRev`) | formalized |
| Definition 3.8, (3.18)–(3.20) | the bimodule `Z_n` | `Frontier.EQDGStructures`, `Frontier.EQOnhDGZn` | formalized |
| Corollary 3.9, (3.21)–(3.23) | `ONH_n ≅ END_{OΛ_n^op}(Z_n)` as dg algebras | `Frontier.EQZnAction` (`corollary_3_9`), `Frontier.EQOnhDGEndIso` (`ONH.toENDZnEquiv`) | formalized |
| (3.24)–(3.27), Remark 3.10 | untwisted and twisted odd Schur polynomials; comparison with EKL | `Frontier.EQSchurDifferential` | formalized |
| (3.28) | the SZ relations | `Frontier.EQSchurDifferential` (`sz_relation_left`, `sz_relation_right`) | formalized |
| Proposition 3.11, (3.29)–(3.31) | `d(s_λ)` | `Frontier.EQSchurDifferential` (`prop_3_11`) | formalized |
| (3.32), Lemma 3.12, (3.33), (3.34) | odd partial derivatives; `d = Σ x_i² ∂/∂x_i` | `Frontier.EQOddDerivatives` | formalized |
| Remark 3.13 | (3.34) on `OPol_n(α)` iff `α = 0` | `Frontier.EQOddDerivatives` (`dAlpha_eq_sum_iff`) | formalized |
| (3.35), Lemma 3.14, (3.36) | `h_β d + d h_β = ⟨α, β⟩` | `Frontier.EQOddDerivatives` (`lemma_3_14`) | formalized |
| Corollary 3.15 | null-homotopy of the identity of `OPol_n(α)` | `Frontier.EQOddDerivatives` (`cor_3_15`), `Frontier.EQFixNullHomotopy` | formalized for the underlying complex; false for null-homotopies of dg modules ([EQ] 4) |
| (3.37), (3.38) | `d(x^a 1_z)`; `Z_n ≅ U_n ⊗ OΛ_n` | `Frontier.EQZnFiniteCell` (`dAlpha_zAlpha_monomial`, `eq_3_38`) | formalized (corrected basis range, [EQ] 3) |
| Proposition 3.16 | `Z_n` finite-cell over `OΛ_n`; `Z_n`, `ONH_n` acyclic for `n ≥ 2` | `Frontier.EQZnFiniteCell`, `Frontier.EQFixZnCells`, `Frontier.EQOnhDGAcyclic` | formalized |
| Proposition 3.17 | `Z_n` cofibrant over `ONH_n` iff not acyclic iff `n ≤ 1` | `Frontier.EQCofibZn` (`prop_3_17`), `Frontier.EQZnFiniteCell` | formalized |
| (3.39)–(3.43) | `ι_{m,n}`, `Ind`, `Res` | `Frontier.EQOPolTensor`, `Frontier.EQOnhTensor`, `Frontier.EQLiftAll` (`iotaAll`), `Frontier.EQThm318` | formalized (definitions) |
| (3.44) | the Künneth isomorphism | `Frontier.EQThm318` (`kunneth`), `Frontier.EQKunnethIntAll` (`kunnethIntAll`) | formalized over every field and over `ℤ` |
| Theorem 3.18 | `u⁺ ≅ K₀(ONH)` as `√−1`-bialgebras | `Frontier.EQThm318`, `Frontier.EQThm318Int`, `Frontier.EQThm318Assembly`, `Frontier.EQK0AssemblySmall` | formalized over every field and over `ℤ`: the structure constants on `{1, E}`, and one isomorphism `u⁺ ≃ K₀(D(ONH))` compatible with `[Ind]` and `[Res]` (`thm_3_18_equiv`, `thm_3_18_mul`, `thm_3_18_comul`; `thm_3_18_int_*`) |
| Remark 4.1 | conventions for thick calculus | `Frontier.EQThickRelations` (`remark_4_1`) | formalized |
| (4.1)–(4.5) | `∂_{w_{a,b}}`, splitters, exploders and the associated functors | `Frontier.EQThickSplitters`, `Frontier.EQThickRelations`, `Frontier.EQThickSlider` | definitions (misprint in the word for `w_{a,b}`, [EQ] 5); the relations displayed after them are formalized, three corrected ([EQ] 6, 7, 8) |
| Proposition 4.2, (4.6), (4.7) | differentials of splitters and mergers | `Frontier.EQThickSplitters` (`prop_4_2_splitter`, `prop_4_2_merger`) | formalized, with the differential of Lemma 2.2 ([EQ] 9) |
| Corollary 4.3, (4.8) | differentials of exploders | `Frontier.EQThickSplitters` (`cor_4_3_split`, `cor_4_3_merge`) | formalized ([EQ] 9) |
| (4.9), Lemma 4.4, (4.10)–(4.12) | `OH_{a,b} ≅ (OΛ_a ⊠ OΛ_b)/M` | `Frontier.EQBorelPresentation` (`lemma_4_4`) | formalized (corrected: `w₀`-semilinear, [EQ] 20) |
| (4.13)–(4.17), Lemma 4.5 | the four variants of odd Schur polynomials | `Frontier.EQZabHat` | formalized (corrected signs, [EQ] 10) |
| (4.18)–(4.20) | hat SZ relation, hat Pieri rule, `d(ŝ_λ)` | `Frontier.EQZabHatFormulas` | formalized ((4.19), (4.20) corrected, [EQ] 17, 18) |
| (4.21), (4.22) | dual bases and their pairing | `Frontier.EQZabCell`, `Frontier.EQZabTrace` (`pairing`) | formalized |
| Definition 4.6 | the dg bimodule `Z_{a,b}` | `Frontier.EQZabModule`, `Frontier.EQFunctorDual` | formalized (left action of `OΛ_a ⊗ OΛ_b` not printed; [EQ] 23) |
| Lemma 4.7, (4.23) | `d` on the basis of `Z_{a,b}`; Pieri rule | `Frontier.EQZabSchur` (`lemma_4_7_box_twisted`, `pieri_twisted`) | formalized |
| Corollary 4.8 | `d`-stable basis; `Z_{a,b}` finite-cell over `OΛ_{a+b}` | `Frontier.EQZabCell`, `Frontier.EQZabFiltration`, `Frontier.EQFixZabCells` | formalized |
| (4.24), (4.25) | the trace `z^∨` and `Z^∨_{a,b}` | `Frontier.EQZabTrace`, `Frontier.EQFunctorDual` (`ZDual`) | definitions (`z^∨` is only `w₀`-semilinear, [EQ] 19) |
| Definition 4.9, (4.26) | `Z^∨_{a,b} ≅ z^∨ · (OΛ_a ⊗ OΛ_b)`, `d(z^∨)` | `Frontier.EQZabTrace` | **partial**: the formula for `d(z^∨)` is used (as the reading of Cor 4.10); that `Z^∨_{a,b}` is free of rank one over `OΛ_a ⊗ OΛ_b` on `z^∨` is not formalized |
| Corollary 4.10 | compatibility of `z^∨` with the dg bimodule structure | `Frontier.EQZabTrace` (`cor_4_10`) | formalized ([EQ] 19) |
| Corollary 4.11 | `Z^∨_{a,b}` cofibrant of graded rank `[a+b, a]_q` | `Frontier.EQZabDual` (`cor_4_11`), `Frontier.EQFunctorDual` | formalized |
| Proposition 4.12 | `REND = END` for `Z_{a,b}`, `Z^∨_{a,b}`; `E_{a,b} ≅ END(Z_{a,b}) ≅ END(Z^∨_{a,b})` | `Frontier.EQZabREnd`, `Frontier.EQZabEndRankOne`; dg-lean `Derived.RightDualEnd` | formalized: (1); (2) `END(Z_{a,b})` is the algebra spanned by the trace-pairing maps (`prop_4_12_two`), and transposition is an isomorphism of dg algebras `END(Z_{a,b}) ≅ END(Z^∨_{a,b})` (`prop_4_12_two_dual`, into the graded opposite in the library's right-action convention for `END`) |
| (4.27), Proposition 4.13 | `Z_a` for compositions: basis, `d`-stability, `HOM(Z_a, Z_b)` | `Frontier.EQZabBlocks`, `…BlocksDiff`, `…BlocksHom`, `…BlocksRank` | formalized ((1) and the graded rank in (3) corrected, [EQ] 11, 21) |
| Definition 4.14 | the multiplication functor | `Frontier.EQFunctorDerived` (`mult`), `Frontier.EQFunctorBox`, `Frontier.EQK0Mult` (`multKHalf`), `Frontier.EQHalfGradedLift` (`IH`) | formalized, on `ℤ`-graded and on half-graded modules |
| Definition 4.15 | `Z^♮_{a,b}` and the comultiplication functor | `Frontier.EQFunctorDerived` (`comult`), `Frontier.EQRestrictionFunctor` (`ZNat`), `Frontier.EQHalfGradedLift` (`RH`) | formalized, on `ℤ`-graded and on half-graded modules (right action not printed and forced, [EQ] 24; misprint [EQ] 25) |
| Lemma 4.16 | `K₀(D(OΛ ⊗ OΛ)) ≅ K₀(OΛ) ⊗ K₀(OΛ)` | `Frontier.EQK0Field` (`lemma_4_16`), `Frontier.EQThm417Int` (`lemma_4_16_int`) | formalized over every field and over `ℤ` |
| Theorem 4.17 | `K₀(D(OΛ)) ≅ U⁺` as twisted bialgebras | `Frontier.EQThm417`, `Frontier.EQThm417Int`, `Frontier.EQK0Assembly` | formalized over every field and over `ℤ` (twist `−1`, [EQ] 1; footnote 5, [EQ] 22) |
| (4.28), (4.29) | module and homotopy categories of `ONH`, `OΛ` as direct sums | — | notation (all statements are componentwise) |
| Definition 4.18 | the functors `J^A`, `J^H`, `J` | `Frontier.EQFunctorEmbedding*`, `Frontier.EQLiftDerived` (`JDAll`), `Frontier.EQHalfGradedLift` (`JH`) | formalized, on `ℤ`-graded and on half-graded modules |
| Corollary 4.19 | `J` fully faithful; on `K₀` it categorifies `u⁺ ⊂ U⁺` | `Frontier.EQFunctorEmbedding` (`jFullyFaithful`), `Frontier.EQFunctorEmbeddingSmall` (`jSmall_isEquivalence`), `Frontier.EQHalfGradedLift` (`jHFullyFaithful`), `Frontier.EQCor419K0` | formalized: fully faithful in every rank, on `ℤ`-graded and half-graded derived categories; on `K₀`, `[J]` is `ι : u⁺ ↪ U⁺` under Theorems 3.18 and 4.17, injective and a map of twisted bialgebras, over `ℤ` and over every field (`cor_4_19_int_*`, `cor_4_19_*`) |
| (4.30), (4.31) | the Morita equivalences `J^A_n`, `J^H_n` | `Frontier.EQFunctorEmbeddingAbelian`, `Frontier.EQZnMorita` | formalized |
| (4.32) | the bimodule `ONH^♮_{a+b}` | `Frontier.EQOnhNat` (`ONHNat`, `d_Pw`), `Frontier.EQRestrictionPoly` | corrected ([EQ] 24) |
| Definition 4.20 | `Res^♮ = ONH^♮ ⊗^L (−)` | `Frontier.EQRestrictionDerived`, `Frontier.EQLiftSmallDerived` (`ResNatDAllAny`), `Frontier.EQHalfGradedLift` (`ResNatH`) | formalized, on `ℤ`-graded and on half-graded modules |
| Corollary 4.21 | `J` intertwines `I` with `Ind` and `R` with `Res^♮` | `Frontier.EQInductionFunctor`, `Frontier.EQRestrictionFunctor`, `Frontier.EQLift*`, `Frontier.EQHalfGradedLift` (`indIsoH`, `resIsoH`) | formalized in all ranks on abelian, homotopy, derived and half-graded derived categories ([EQ] 23, 24) |
| Lemma A.1 | adding or removing boxes of one colour | `Frontier.EQLimaPartitions` (`lemma_A_1`) | formalized |
| Proposition A.2 | Lima bases of `H(OΛ)`, `H(OΛ_n)` | `Frontier.EQLimaCohomology`, `Frontier.EQLimaOsym`, `Frontier.EQLimaAllRanks`, `Frontier.EQLimaLimit` | formalized |
| Proposition A.3, (A.1) | `H(OΛ)` is a polynomial algebra | `Frontier.EQLimaPolyAlg` (`prop_A_3_columns`, `prop_A_3_rows`, `tri_mul`) | formalized (two claims of the proof refuted, [EQ] 12) |
| (A.2), (A.3), (A.4) | `p`-dg setting; slash cohomology | `Frontier.EQPdgSlash` | (A.2), (A.3) definitions ((A.3) misprint, [EQ] 15); (A.4) formalized |
| (A.5)–(A.7) | `d(e_k)`, `d(h_k)`, `d(s_λ)` in the `p`-dg setting | `Frontier.EQPdgPoly`, `Frontier.EQPdgAlt`, `Frontier.EQPdgLimit` | formalized ((A.5), (A.6) corrected, [EQ] 16) |
| Theorem A.4 | slash cohomology of `Sym_n` and `Sym` | `Frontier.EQPdgTheorem`, `Frontier.EQPdgTheorem2`, `Frontier.EQPdgLimitTheorem` | formalized |

Not formalized: the freeness claim of Definition 4.9. Remarks 2.1, 2.9, 2.15 and Examples 2.10–2.12 are not targets.

### [BE2] (in progress)

Names are in `OddMath.SKM`. Diagrams are read bottom to top, words left to right (as in the
paper's pictures); a strand colour records the weight of the region to its right. The ground ring is
a commutative ring concentrated in even parity, and the weight data is any additive group with
simple roots and coroots (lie-lean's `CartanDatum`) whose Cartan matrix is generalized Cartan; the
paper's realization in a complex vector space is a special case.

| Statement | Content | Declarations |
| --- | --- | --- |
| §1, data before Def 1.5 | parity on `I`, (1.4), `tᵢⱼ` (1.5), `sᵢⱼ^{pq}` (1.6), `2` invertible if some `i` is odd | `Datum`, `Scalars` |
| Def 1.5, (1.7)–(1.14) | the Kac–Moody 2-supercategory `𝔘(𝔤)` by generators `x`, `τ`, `η`, `ε` and relations: quiver Hecke superalgebra relations (1.7)–(1.9), right adjunction (1.10), `σ` (1.11), inversion relations (1.12)–(1.14) with the inverse matrix entries of (2.6)–(2.9) as generators; all relations parity-homogeneous; a strict 2-supercategory | `sig`, `Rel`, `relation`, `pres`, `isParityHomogeneous`, `U`, `twoSupercategory` |
| §1 "Gradings", (1.31) and the degree table | symmetrization `dᵢ`, homogeneity condition (1.31); degrees of `x`, `τ`, `η`, `ε` as in the table, and the degrees forced by the inversion relations on the inverse entries (leftward crossing `0`, `♦`-cup `dᵢ(⟨hᵢ,λ⟩-1-2n)`, `♦`-cap `-dᵢ(⟨hᵢ,λ⟩+1+2n)`); every relation homogeneous; `𝔘(𝔤)` a graded 2-supercategory (no field hypothesis needed) | `Symmetrizer`, `Scalars.Homogeneous`, `gdeg`, `isHomogeneous_gdeg`, `UGr`, `UGr.instGradedTwoSupercategory` |
| Def 1.6 | the `(Q, Π)`-envelope `𝔘_{q,π}(𝔤)` (string-diagrams-lean's `QPiTwoEnvelope`), its underlying `(Q, Π)`-2-category `𝔘̲_{q,π}(𝔤)` and `𝔘̇_{q,π}(𝔤)` (idempotent completion of the additive envelope) | `Uqπ`, `UUnderline`, `UDot` |
| (1.1)–(1.3) in normal form | rewriting calculus for normal-form diagrams: placement, rewriting in context, the super interchange law for adjacent layers and for blocks with the sign `(-1)^{\|A\|\|B\|}`; the relations (1.7)–(1.14) as equations of normal-form diagrams | `cl`, `ctxL`, `cl_step`, `cl_swap`, `cl_interchange`, `cl_zigE`, `cl_quadNe`, `cl_invP₁`, … |
| Def 2.1, (2.1)–(2.5) | downward dots and crossings as right mates; (2.2) `n`-th powers of downward dots are `(-1)^{\|i\|⌊n/2⌋}` times the mate of `xⁿ`; (2.3) dots slide around rightward cups and caps (and in mate form for any 2-morphism); (2.4), (2.5) pitchfork relations; composition of mates `mate(a) ≫ mate(b) = (-1)^{\|a\|\|b\|} mate(b ≫ a)` | `mateL`, `ddotL`, `dcrossL`, `cl_ddot_pow`, `eq_2_3_a`, `eq_2_3_b`, `cl_cup_slide`, `cl_cap_slide`, `eq_2_4_a`, `eq_2_4_b`, `eq_2_5_a`, `eq_2_5_b`, `cl_mate_comp` |
| Def 2.2, (1.17), (2.10)–(2.14) | the units `c_{λ;i}`; `η'`, `ε'`; (2.12)–(2.14) | `CScalars`, `etaP`, `epsP`, `eq_2_12_a`, `eq_2_12_b`, `eq_2_13_a`–`eq_2_13_c`, `eq_2_14_a`–`eq_2_14_c` |
| Def 2.3, (2.15)–(2.18) | dotted bubbles for all `n ∈ ℤ` (negatively dotted bubbles), the shorthand `n + *`, the odd bubble; the two definitions of the odd bubble agree at `⟨hᵢ, λ⟩ = 0` | `bubL`, `bubR`, `bubLs`, `bubRs`, `oddBubble`, `oddBubble_consistent` |
| Lemma 3.1 (3.1)–(3.6) | dots slide through upward crossings ((3.1), (3.2); the heights of the dots in the correction terms as in the paper), upward and downward dots through `σ` ((3.3), (3.4)), downward dots through downward crossings ((3.5), (3.6)); all `i`, `j`, with the correction terms exactly as printed | `lemma31_eq1_ne`, `lemma31_eq1_eq`, `lemma31_eq2_ne`, `lemma31_eq2_eq`, `lemma31_eq3_ne`, `lemma31_eq3_eq`, `lemma31_eq4_ne`, `lemma31_eq4_eq`, `lemma31_eq5_ne`, `lemma31_eq5_eq`, `lemma31_eq6_ne`, `lemma31_eq6_eq` |

## Building

Requires [elan](https://github.com/leanprover/elan). Toolchain `leanprover/lean4:v4.34.1` and Mathlib
`v4.34.1` (`d13f23b723b8a846827a245b89c10fc7d3f11612`) are pinned. The diagrammatic modules depend on
string-diagrams-lean at `1f45e3c8ba51a148d028ce4f9bda36002f275690`, the [EQ] dg structures on
[dg-lean](https://github.com/apellis/dg-lean) at `38e1e848d07386de5053f85099a947d92afced40`, and the
[BE2] Cartan data on [lie-lean](https://github.com/apellis/lie-lean) at
`9caf9bf648b6fb29c9d2436565c99b0b0e892f9c` (see `lakefile.lean` and `lake-manifest.json`).

```sh
lake exe cache get
lake --wfail build
python3 scripts/audit_axioms.py
```

`lakefile.lean` keeps warnings as errors and preserves the pre-4.34 elaborator
implicit-argument unfolding via `backward.isDefEq.respectTransparency=false` and
`backward.isDefEq.respectTransparency.types=false`; these do not change kernel checking.
The audit inventories every local `OddMath` source module and traverses the transitive axiom
closure of every declaration owned by those modules, including private/generated declarations
and declarations in other namespaces. It fails on any axiom other than `propext`,
`Classical.choice`, or `Quot.sound`, missing modules, or source changes during the audit.
Standalone audit modules with colliding local-instance names are checked in separate import
environments rather than being omitted. Reports, source hashes, and a per-declaration axiom
inventory are written to `.verification/axioms/`. This checks proof trust, not whether a theorem
has the same mathematical statement as a prior version.

## Models used

The code and proofs were produced with AI models under human direction and checked by Lean:

- GPT-6 Astra
- Muse Spark 1.3
- Claude Opus 5.5

## License

Released under the Apache License 2.0; see [`LICENSE`](LICENSE).
