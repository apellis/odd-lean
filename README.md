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
  (Thm 3.18 and Thm 4.17 are proved, over every field and over `ℤ`; every numbered statement other
  than Remarks 2.1, 2.9, 2.15 and Examples 2.10–2.12 is formalized, some in corrected form; see
  the [EQ] coverage table below).
- **[BE2]** J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2 (in
  progress; see the [BE2] status below).
- **[CHW1]** S. Clark, D. Hill, W. Wang, *Quantum supergroups I. Foundations*, arXiv:1301.1665v2,
  and **[C]** S. Clark, *Quantum supergroups IV. The modified form*, arXiv:1312.4855v2 (the
  covering quantum group used in [BE2] §§9–12).
- **[CHWII]** S. Clark, D. Hill, W. Wang, *Quantum supergroups II. Canonical basis*,
  arXiv:1304.7837v2 (highest-weight polarizations and their half-form limit).

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

### [EQ]

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
  `EQDiagonal.onh n` places `ONH_{n+2}`'s ordinary degree `k` at `(2k, k mod 2)`; its dots
  and crossings have bidegrees `(2,1)` and `(-2,1)`. The differential is unchanged,
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
  `OPol_N` dg ring with `N ≤ 1`, `cohomologyZeroEquivInt` identifies `H⁰` with `ℤ`,
  taking the constant class to its integer, and `cohomology_eq_zero_of_ne_zero` proves
  vanishing in every nonzero cohomological degree. The existing Lima theorem supplies a
  boundary-plus-constant normal form with a unique integral constant; homogeneous projection
  supplies graded boundaries. `Frontier.EQSmallRankQuasiIso` proves the unit
  inclusion `ℤ → OPol_N` is a dg-ring quasi-isomorphism (`intInclusion_isQuasiIso`). Keller's
  theorem gives the ordinary derived equivalence and the ordinary compact `K₀` equivalence
  (`derivedEquivalence`, `compactK0Equiv`), taking the regular integral class to the regular
  polynomial class (`compactK0Equiv_self`). This does not compute `K₀(ℤ)` numerically or supply
  the half-graded derived equivalence, half-graded compact `K₀` calculation, or tensor formula.
- `Frontier.EQHalfGradedUnit` constructs the integral unit dg functor on the weight
  categories of the diagonal half-gradings, in every rank. It maps placed integer components
  to the corresponding polynomial components, preserving multiplication, differential,
  cohomological degree, weight, and both periodicity units.
- `Frontier.EQHalfGradedUnitQuasiEquivalence` proves that this unit functor is a dg
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
- `Frontier.EQHalfGradedUnitParity` proves that derived restriction along the unit
  commutes with every internal shift and the existing parity shift in every rank. In ranks
  zero and one, the unit and counit of Keller's equivalence give these comparisons for
  derived induction as well. Neither shift is defined by transport. Restriction
  to compact objects and descent to super-`K₀` are supplied by the next module;
  these natural isomorphisms do not assert parity-involution coherence or a numerical formula.
- `Frontier.EQHalfGradedUnitSuperK0` restricts the internal-shift and parity
  comparisons to compact objects for `N ≤ 1`. The existing `compactK0Equiv` maps the
  parity-relation subgroup onto its target counterpart, giving `superK0cEquiv`
  between the existing compact super Grothendieck groups. Every compact object class
  maps to its perfect induction. No replacement quotient or transported shift
  is used. (Numerical calculations and the Künneth isomorphism: `Frontier.EQThm318Int`,
  `Frontier.EQKunnethIntAll`.)
- `Frontier.EQHalfGradedUnitParityCoherence` proves, in every rank, that module
  restriction along the integral unit respects both existing parity involutions.
  The proof uses preservation of the inverse periodic unit, and gives the complete
  natural-isomorphism square and its image under the localization functor `Q`.
  Module and source-localization universes remain independent. The separate modules
  below identify the derived comparison and prove its involution coherence, under
  that comparison's source-universe constraint. Low-rank induction
  parity-involution coherence is supplied by the induction module below.
- `Frontier.EQHalfGradedRestrictionCoherence` computes the existing derived
  restriction-composition isomorphism on localized modules, using the existing
  module comparison. It also proves coherent-shift compatibility of the existing
  module-localization restriction comparison. The consumer checks both compositions
  of the integral unit with weight translations, in every rank and with
  independent source/target localization universes.
- `Frontier.EQHalfGradedUnitDerivedParityCoherence` identifies the existing
  `restrictParityIso` on localized modules with the module parity comparison
  through the existing localization isomorphisms, in every rank. It retains the
  equality of source Hom and module universes, with independent target
  Hom universe. It also computes the existing `parityShiftDIso` on localized modules
  with independent module/derived Hom universes.
- `Frontier.EQHalfGradedUnitDerivedParityInvolution` pastes those formulas with the
  module involution square and descends by the localization universal property.
  The existing `restrictParityIso` consequently intertwines the derived
  `parityShiftDIso` involutions on every derived target object, in every rank. Both
  the full natural-isomorphism square and its component formula are proved. The
  source derived Hom universe equals the module universe, as in the existing
  comparison; the target Hom universe is independent. No comparison or involution
  is replaced.
- `Frontier.EQHalfGradedUnitInductionParityInvolution` proves the componentwise and
  full natural-isomorphism involution squares for derived induction when
  `N ≤ 1`, using the existing `derivedEquivalenceParityIso` and both existing
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
| Definition 4.9, (4.26) | `Z^∨_{a,b} ≅ z^∨ · (OΛ_a ⊗ OΛ_b)`, `d(z^∨)` | `Frontier.EQZabFree` (`def_4_9_mem`, `def_4_9_free`), `Frontier.EQZabFrobenius`, `Frontier.EQZabTrace` (`cor_4_10`) | formalized for `a + b ≥ 2` with the corrected generator `w₀ ∘ z^∨` ([EQ] 19): every right `OΛ_{a+b}`-linear map `Z_{a,b} → OΛ_{a+b}` is `x ↦ w₀ z^∨(g x)` for a unique `g ∈ OΛ̃_a ⊠ OΛ̃_b`, so `Z^∨_{a,b}` is free of rank one over `OΛ_a ⊗ OΛ_b` on `w₀ ∘ z^∨`; (4.26) is Cor 4.10. For `a + b ≤ 1`, `OΛ_a ⊗ OΛ_b = OΛ_{a+b}` and the claim is trivial |
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

Remarks 2.1, 2.9, 2.15 and Examples 2.10–2.12 are not targets.

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
| Mates of 2-morphisms between words | mates with respect to blocks of cups and caps (composition `mate(A) ≫ mate(B) = (-1)^{\|A\|\|B\|} mate(B ≫ A)`); nested cups and caps for words of upward strands and their zigzag relations; the downward crossing is the mate of the upward crossing; mates of `A ⊗ 1` and `1 ⊗ A`; clockwise rotation of one strand (`σ` is the rotation of `τ`) and its composition rule | `mateB`, `cl_mateB_comp`, `cupN`, `capN`, `zigE_N`, `zigF_N`, `mateN`, `dcrossL_eq_mateN`, `cl_mateN_comp`, `cl_mateN_whiskerL`, `cl_mateN_whiskerR`, `rotL`, `sigmaL_eq_rotL`, `cl_rotL_comp` |
| Lemma 3.2 (3.7) | the rotated quadratic relation on two downward strands, all cases, signs as printed (in the last sum the dots on the right strand come first: they are at the same height in the paper) | `lemma32_eq`, `lemma32_zero`, `lemma32_ne` |
| Lemma 3.3 (3.8), (3.9) | the braid relation with one downward strand (3.8) and with three downward strands (3.9), including the correction terms for `i = k ≠ j` with the signs as printed (dots at the same height: the rightmost first) | `lemma33_eq8`, `lemma33_eq8_eq`, `term8`, `lemma33_eq9`, `lemma33_eq9_eq`, `dots3` |
| Def 3.4, Prop 3.5, (3.10) | the super-opposite `𝒜^{sop}` (string-diagrams-lean `SOp`, `f^{sop} ∘ g^{sop} = (-1)^{\|f\|\|g\|}(g ∘ f)^{sop}`) and contravariant superfunctors out of a presented category given by images of generators (`SOpMap.liftGen`); the Chevalley involution `ω : 𝔘(𝔤) → 𝔘(𝔤)^{sop}`: `λ ↦ -λ`, `Eᵢ ↔ Fᵢ`, `x ↦` downward dot, `τᵢⱼ ↦ -(-1)^{\|i\|\|j\|}` downward crossing, `η ↦ ε`, `ε ↦ η` as printed, and on the inverse entries leftward crossing `↦ -`leftward crossing, `♦`-cup/cap `↦ (-1)^{\|i\|n}` `♦`-cap/cup; every relation of Def 1.5 maps to zero; `ω` preserves parity and commutes with whiskering; its value on every normal-form diagram, (3.10), and `ω(σᵢⱼ) = -(-1)^{\|i\|\|j\|}σⱼᵢ`; `ω² = id` on every 2-morphism (the double images of `x` and `τ` straightened by (2.3), (2.4), (2.5), (1.10); every diagram between the 1-morphisms `E_s 1_λ` is in normal form). The values on `η'`, `ε'` and bubbles listed after Prop 3.5 are not separate declarations | `chevMap`, `chevImg`, `omega`, `omega_relation`, `omega_cl`, `omega_gen`, `omega_dots`, `omega_sigma`, `omega_whisk`, `omega_mem`, `omega_omega`, `omega_omega_cl`, `diag_eq_mkD` |
| Prop 4.1 (4.1)–(4.4) | leftward dot slides, all `i`, `j`, `n`, `λ`: (4.1), (4.2) through the leftward crossing (correction terms with `ε'` and `η'`, `i = j`), (4.3), (4.4) around the leftward cap `ε'` and cup `η'`, with `(-1)^{⌊n/2⌋}`, `(-1)^{⟨hᵢ,λ⟩}` and twice the odd bubble (2.18) for odd `i` and odd `n`; signs as printed. Both signs of `⟨hᵢ,λ⟩` are proved directly (the paper uses the Chevalley involution for half of them); the odd bubble squares to zero (1.24) | `lemma41_eq1`, `lemma41_eq1_ne`, `lemma41_eq2`, `lemma41_eq2_ne`, `lemma41_eq3_even`, `lemma41_eq3_odd`, `lemma41_eq4_even`, `lemma41_eq4_odd`, `oddBubble_comp_self` |
| Prop 5.1 (5.3)–(5.10) | (5.3), (5.4): `n + *` dotted bubbles vanish for `n < 0` and are `c_{λ;i}^{±1}` for `n = 0`; homogeneous closed 2-morphisms on `1_λ` supercommute (all bubbles homogeneous, the odd bubble odd, (1.24)); the two identities (5.8) from the proof (the second one by the mirrored computation instead of the Chevalley involution, with the bubbles in the opposite vertical order); (5.5) for even `i`; for odd `i`: (5.9) and (5.10) for all `N ∈ ℤ` (the range the paper obtains from the Chevalley involution by the mirrored induction), (5.7), (5.6); the identity `∑_{r+s=t} (-1)^{\|i\|r} bubRs(s) ≫ bubLs(r) = 0` used for Corollaries 5.2 and 5.4 | `bubLs_neg`, `bubLs_zero`, `bubRs_neg`, `bubRs_zero`, `closedPar`, `comm_of_mem`, `bubL_mem`, `bubR_mem`, `oddBubble_sq`, `ig_hpos`, `ig_hneg`, `eq_5_5`, `eq_5_6`, `eq_5_7_a`, `eq_5_7_b`, `eq_5_9`, `eq_5_9_all`, `eq_5_10`, `bubble_key` |
| (1.19), (1.20), (5.1), (5.2) | `Sym` (polynomial algebra in `e₁, e₂, …`; `h_n` defined by Macdonald (I.2.6′)), `Sym[d]`; the homomorphisms `β_{λ;i}` (even `i`: `Sym → End(1_λ)`; odd `i`: `Sym[d] → End(1_λ)`, well defined by the super interchange law and (1.24)), unique with the given images of `e_n` (and `d`); the images of `h_n`, `d e_n`, `d h_n` as in (1.19), (1.20); (5.1), (5.2) | `Sym`, `Sym.e`, `Sym.h`, `Sym.e_h_rel`, `SymD`, `beta`, `beta_unique`, `beta_e`, `beta_h`, `betaD`, `betaD_unique`, `betaD_d`, `betaD_e`, `betaD_h`, `betaD_de`, `betaD_dh`, `eq_5_1_even`, `eq_5_2_even`, `eq_5_1_odd_even`, `eq_5_1_odd_odd`, `eq_5_2_odd_even`, `eq_5_2_odd_odd` |
| Cor 5.2, Cor 5.3, Cor 5.4 (5.17) | (5.11), (5.12): the `♦`-cups and caps as sums of dotted bubbles times `η'` (resp. `ε'`) with dots, via the inverse-matrix characterization ((5.13), (5.14) and their analogues for (5.12), which the paper leaves as "entirely similar"); (5.15), (5.16); the curl relations (5.17) `σ ≫ ε'` and `η' ≫ σ` | `eq_5_11`, `eq_5_12`, `eq_5_13`, `eq_5_14`, `eq_5_13'`, `eq_5_14'`, `dcupRHS`, `dcapRHS`, `eq_5_15`, `eq_5_16`, `eq_5_17_a`, `eq_5_17_b` |
| Cor 5.4 (5.18)–(5.21) | the dotted left and right curls on `Eᵢ 1_λ` as sums of dots times dotted bubbles, all four as printed (heights of dots and bubbles as in the paper); tools: homogeneous linear combinations of diagrams (`homPar`), placement compatible with composition, and the super interchange law for placed 2-morphisms | `eq_5_18`, `eq_5_19`, `eq_5_20`, `eq_5_21`, `curlL_eq`, `curlR_eq`, `homPar`, `plcL_comp_of_mem`, `plcL_left_interchange`, `plcL_right_interchange`, `etaP_mem`, `epsP_mem` |
| Lemma 6.1, Prop 6.2 | the claim (6.3) for `⟨hᵢ,λ⟩ ≤ -1` by testing against the isomorphism (1.14) ((6.4), (6.5)); the pitchfork relation (6.1); the mirror-image claim for `⟨hᵢ,λ⟩ ≥ -1` by testing against (1.13), and (6.2); the first relation of (6.6) (left adjunction zigzag on `Eᵢ`, sign `(-1)^{\|i,λ\|}`) in all three cases of the paper; the second relation of (6.6) (zigzag on `Fᵢ`, no sign) as the image under `ω` of the first relation at `-λ`, computed on normal-form diagrams in the three cases `⟨hᵢ,λ⟩ = 1`, `≤ 0`, `≥ 2` | `eq_6_3`, `check_6_4`, `check_6_5`, `ext_EFE`, `eq_6_1`, `claim_6_2`, `ext_EFE'`, `eq_6_2`, `eq_6_6_a`, `retaF`, `lepsF`, `eq_6_6_b` |
| Lemma 7.1 (7.1), (7.2) | an upward strand past a leftward cap or cup for distinct colours, with the stated weight bounds; the two relations are proved separately using inversion-map components, the mixed braid relation and bubble evaluations | `eq_7_1`, `eq_7_2` |
| Prop 7.2 (7.5)–(7.6) | all four pitchfork equalities, for every weight and every pair of colours, with the sign in (7.6); left adjunction removes the weight bounds, and the Chevalley involution gives the downward orientations | `eq_7_5_a`, `eq_7_5_b`, `eq_7_6_a`, `eq_7_6_b`; `Om_etaP`, `Om_epsP` |
| (1.26)–(1.28), cyclicity | the downward dot and crossing defined with the leftward cups and caps `η'`, `ε'` (left mates) against Definition 2.1 (right mates): (1.26), (1.27) as printed (odd dot: twice the odd bubble on the left minus the left mate); (1.28) with the sign `(-1)^{\|i\|\|j\|(⟨hᵢ,λ⟩+⟨hⱼ,λ⟩+1)}`, as printed when `i` or `j` is even; the printed relation forces `1 = 0` on `FᵢFᵢ1_λ` for odd `i`; see ERRATA [BE2] 3 | `ldot`, `obLeft`, `eq_1_26`, `eq_1_27`, `lcrossMate`, `eq_1_28`, `eq_1_28_of_even`, `eq_1_28_self`, `eq_1_28_printed_self_odd`, `eq_1_28_printed_odd`, `rot_tau_left` |
| Prop 7.3(iii), (7.11)–(7.12), `dᵢⱼ = 1` | both connected-colour bubble slides at every weight and integer shifted degree, including fake bubbles; arbitrary `dⱼᵢ`, either parity of `j`, and unchanged scalars | `eq_7_11_of_d_one`, `eq_7_12_of_d_one` |
| Prop 7.3(iii), (7.11)–(7.12), general connected pairs | both slides at every weight and integer shifted degree, including fake bubbles, with the full rectangular polynomial, arbitrary colour parities and unchanged scalars | `eq_7_11_connected`, `eq_7_12_connected`, `bubbleCoeff_connected` |
| Prop 7.3(iii), proof, middle weights | arbitrary dotted braid contraction, evaluated curl sum, shifted convolution and coefficient induction through every missing degree | `bubble_slide_middle_dotted_all`, `bubble_slide_middle_shift_convolution`, `bubbleCoeff_middle` |
| Prop 7.3(iv), corrected (7.13)–(7.14) | both disconnected-colour bubble slides, every weight and shifted degree `n ≥ 0`, including fake bubbles; a factor `tᵢⱼ` on each RHS, with no scalar specialization; see ERRATA [BE2] 1 | `eq_7_13_corrected`, `eq_7_14_corrected` |
| Prop 7.3(i–ii), (7.7)–(7.10) | both same-colour slides, all weights and shifted degrees `n ≥ 0`, including fake bubbles; coefficients `r+1` for even colour and `2r+1` at even dot counts for odd colour, with the boundary correction at coroot value −1 retained | `eq_7_7`, `eq_7_8`, `eq_7_9`, `eq_7_10` |
| Cor 7.4, (7.15), odd-bubble centrality | the normalized odd bubble slides across every `Eⱼ` and `Fⱼ`, with unchanged scalars; supernatural action on homogeneous 2-morphisms of arbitrary parity between arbitrary words with matching boundary weight, and the even-plus-odd linearity formula | `oddBubble_slide_up`, `oddBubble_slide_down`, `oddBubble_naturality`, `oddBubble_naturality_add` |
| Prop 7.6, alternative braid relation | the braid relation on `Eⱼ Fᵢ Eₖ 1_μ` with the downward strand on either side of the upward crossing, for all colours, weights and parities and arbitrary scalars: equal for `(i,j,k)` not all equal (the case `i = k ≠ j` by rotating the upward braid relation with the left cup and (7.5)), and the two triple sums for `i = j = k`; the second sum has the sign `(-1)^{\|i\|(h+r+s)}`, see ERRATA [BE2] 2 | `AltBraid.prop_7_6`, `AltBraid.prop_7_6_ne`, `AltBraid.prop_7_6_equal`, `AltBraid.left_braid`, `altL`, `altR`, `altCorrectionR`, `altCorrectionL` |
| Thm 8.1, proof infrastructure: lower terms, local relations, cap elimination, bending | infrastructure for the spanning argument (the proof the paper omits, after KL III Prop 3.11): every 2-morphism is a combination of normal-form diagrams; diagrams with the leftward cup `η'` and cap `ε'` as crossingless layers, their crossing count (upward and leftward crossings) and the spans `LeL` of diagrams with at most `c` crossings, closed under composition, placement and rewriting in context; modulo diagrams without crossings: dot slides through upward, sideways, downward and leftward crossings ((1.8), (3.1)–(3.6), (4.1), (4.2)), double crossings ((1.7), its mate, (1.12)–(1.14)), the braid relations (1.9), (3.8), (3.9) and Prop 7.6, curls (5.18)–(5.21); bubbles, `η'`, `ε'` are crossingless; the pitchforks (7.5) as identities of extended diagrams. Bubble slides: Prop 7.3/Cor 7.4 move any element of the image of β (1.21) to the rightmost region, and the span of products of bubbles equals that image. Cap elimination (KL III Prop 3.11) is proved with no hypotheses (`capElim_full`): Reidemeister 3 in all orientations up to lower terms (`r3Rel`, by rotating (1.9) and Prop 7.6) and the curls of a crossing with a cap or a cup (`capCurlRel`, `cupCurlRel`). One-sided spanning: every 2-morphism `1_μ → E_v 1_μ` lies in the right SYM-span of canonical chord diagrams with dots at the left ends of the arcs (`diagBubSpan_canonDiagrams_eq_top`, stated with the three local relations as arguments). Bending: nested cups and caps with exact super signs transport spanning from `Hom(1, E_{s* t})` to `Hom(E_s, E_t)` (`diagBubSpan_bendL_eq_top`). (1.21)–(1.22), crossingless case: closed crossingless diagrams lie in the image of β, so β_ν is surjective once crossings are removed. The theorem itself is the next row | `mem_span_cl`, `plcL_comp`, `XShape`, `xev`, `xcnt`, `LeL`, `leL_comp`, `plcL_leL`, `xev_mod_ctx`, `xev_mod_at`, `exists_mem_leL`, `dsUp0`, `dsUp1`, `dsSigma0`, `dsSigma1`, `dsDn0`, `dsDn1`, `dsLcross0`, `dsLcross1`, `r2Up`, `r2Dn`, `r2Sigma`, `r2Lcross`, `r3Up`, `r3Dn`, `r3Mixed`, `r3Alt`, `bubL_mem_leL`, `bubR_mem_leL`, `curl_5_18`–`curl_5_21`, `pitchfork_cap`, `pitchfork_cup`; `IsBubbleProd`, `bubAt`, `comp_bubAt`, `xev_ichg`, `xDotL`, `xCrL`, `xCupL`, `xCapL`, `Mv`, `MvSp`, `thruShort`, `CapTarget`, `mvSp_comp`, `capBlk`, `capTarget_comp_dcup` ((5.11)), `capTarget_comp_dcap` ((5.12)), `pushHyp_nil`, `push_disjL`, `push_disjR`, `push_dotA`, `capElim`, `bubbleProdSpan_eq`, `isBub_iff_mem_bubbleProdSpan`, `plcL_mem_mvSp_of_isBub`, `bubbleSlideOut`, `capElim_of_push`, `XEq`, `pushHyp_all`, `capElim'` (hypotheses `R3Rel`, `CapCurlRel`, `CupCurlRel`), `CupSpan`, `cupSpan_cap`, `cupSpan_dcup`, `cupSpan_dcap`, `xev_isBub_of_xcnt_eq_zero`, `leL_zero_le_bubbleSpan`, `bubbleSpan_eq_top_of_mem_leL_zero`, `XSgn`, `r3Rel`, `capCurlRel`, `cupCurlRel`, `capElim_full`, `chordLay`, `equiv_sound`, `chordLay_normal_form`, `arc_dot`, `plcL_oddBubble`, `diagBubSpan_canonDiagrams_eq_top`, `dualW`, `cupA`, `capA`, `zigA_block`, `zigB_block`, `bendF`, `bendG`, `bendG_bendF`, `bendF_bendG`, `diagBubSpan`, `bendL`, `diagBubSpan_bendL_eq_top` |
| Thm 8.1 | `Hom(E_a 1_λ, E_b 1_λ)` is generated as a right `SYM`-module (`β_λ` acting in the rightmost region, `diagBubSpan`) by the decorated matchings `f(σ, λ)`, `σ ∈ M̂(a, b)`, for any set `M` of reduced `(a, b)`-matchings representing the equivalence classes (same pairing) and any distinguished points on the strands, with the paper's notion of reduced (`StrictReduced₂`: no self-crossings, distinct strands cross at most once, at most one critical point per strand). Matchings are generic layerings of cups, crossings and caps. Also proved: every pairing of `a* b` is the pairing of a strictly reduced matching, so every matching is equivalent to a reduced one (the remark before Thm 8.1). Generalizations only: `M` may contain equivalent matchings, dots at one height in any order, `wt(a) = wt(b)` not assumed. Other forms: `theorem_8_1_of_reduced` (weaker notion `Reduced₂`), `theorem_8_1_of_pairings` (M representing every pairing), `theorem_8_1_nil_bottom` (`a = ∅`) | `theorem_8_1`, `StrictReduced₂`, `critPts₂`, `exists_strictReduced_matching`, `exists_strictReduced_equiv`, `theorem_8_1_of_reduced`, `theorem_8_1_of_pairings`, `theorem_8_1_nil_bottom`, `exists_reduced_matching`, `reduced_of_length_xs_eq_cr`, `reduced₂_normal_form`, `reduced₂_bent_normal_form`, `canon_dots_mem_decorated₂`, `DotBase.dots_up`, `eq_top_of_canon_dots_mem`, `Reduced₂`, `IsMatching₂`, `pairing₂`, `OnStrand₂`, `Decorates₂`, `decoratedFamily₂`, `reduced_iff`, `reduced_canon`, `equiv_canon_of_reduced`, `diagBubSpan_canonDiagrams_eq_top'`, `diagBubSpan_bendL_canonDiagrams_eq_top` |

| Theorem | Source | Declaration | Hypotheses | Status |
| --- | --- | --- | --- | --- |
| Lemma 9.1, extension into a super-opposite | [BE2] Lemma 9.1 | `qpiTwoSOp`, `extendEnvelopeSOp`, `twoJ_comp_extendEnvelopeSOp`, `extendEnvelopeSOp_isGraded`, `exists_graded_envelopeSOp_extension` | `CommRing R`; graded 2-supercategories; a graded 2-superfunctor into the already-shifted super-opposite | Proved: the target has its `(Q, Π)`-structure, and the extension is graded and restricts to the given 2-superfunctor, including comparison data |
| Lemma 9.6, extension into a super-reverse | [BE2] Definition 9.5 and Lemma 9.6 | `TwoSRev`, `extendEnvelopeSRev`, `twoJ_comp_extendEnvelopeSRev`, `extendEnvelopeSRev_isGraded`, `exists_graded_envelopeSRev_extension` | `CommRing R`; graded 2-supercategories; a graded 2-superfunctor into the already-shifted super-reverse | Proved: reversed 1-morphisms and Koszul-signed horizontal composition, unchanged vertical composition and `(Q, Π)` structure maps; the extension is graded and restricts to the given functor, including comparison data |
| Prop 9.4, generator and relation checks | [BE2] Prop 9.4, proof (unnumbered assignments); (1.7)–(1.12) | `psiObj`, `psiMap`, `psiDot_power`, `psiCross_sq`, `psiCross_quadZero`, `psiCross_quadNe`, `psi_slideL`, `psi_slideR`, `psi_slideLEq`, `psi_slideREq`, `psi_braid`, `psi_braidEq`, `psiBraidCorrection`, `psiCup`, `psiCap`, `psiAdjunction_up_whisker`, `psiAdjunction_dn_whisker`, `psiSigma_eq_composite`, `psiMixed_inversion`, `psiSigma_mem_parity`, `psiSigma_mem_degree`, `psiLCross_mem_parity`, `psiLCross_mem_degree` | `CommRing k`, `Datum`, `Scalars`, `Symmetrizer`, `Scalars.Homogeneous`; `CScalars` for cups/caps and the mixed composite; `t² = −1` for powers and relations | All upward quadratic/dot-slide/braid cases proved, with actual whiskerings and assigned-dot correction powers in source order. Cups/caps are even and of the source degrees; all four whiskerings and both actual adjunction composites are checked. The mixed crossing is computed from the printed assignments in the shifted super-opposite; both distinct-colour inverse equations are proved. Same-colour target inversion and totalized zero entries are proved in the row below. The complete presentation-ideal kernel is proved below. Quotient Hom maps and their vertical/graded laws are proved below; the strict graded bare ψ 2-superfunctor is proved below. Its shifted envelope extension and both literal inverse-functor equalities, including coherence, are recorded below. |
| Prop 9.4, raw same-colour inversion | [BE2] (1.13)–(1.14), Cor 5.2 and (5.11)–(5.14) | `psiSameCup_inversion`, `psiSameCap_inversion`, `psiSameCupDual_zero`, `psiSameCapDual_zero`, `psiSameCupDual_mem`, `psiSameCapDual_mem` | `CommRing k`, `Datum`, `Scalars`, compatible `CScalars` | Both raw five-block inverse matrices, ordered bubble-sum dual entries, parity and totalized zeros proved, including zero weight. The separately proved shifted-target transport is recorded below. |
| Prop 9.4, inverse coefficient and parity calculations | [BE2] Prop 9.4; Lemma 9.1 and Remark 9.2 | `psiDots_inverse_coeff`, `psiCross_inverse_coeff`, `psiShift_involutive`, `psiShift_comp`, `psiEnvelope_twice_zeta_hom`, `psiPiConjugate_eq`, `psiCup_piConjugate`, `psiCap_piConjugate` | Existing `CommRing k`, datum, homogeneous scalars and symmetrizer; compatible `CScalars` for cups/caps; `t² = −1` for coefficient cancellation | Opposite-root cancellation, signed-word involution, actual double-Π reversal and parity conjugation proved with boundary transports. These are calculations on assigned images, not the original derived left-image calculation or literal two-sided functor identities. |
| Prop 9.4, integer/parity extension calculations | [BE2] Lemma 9.1 and Remark 9.2 | `psiQIso_hom_eq`, `psiQIso_inv_eq`, `psiQPiConjugate_eq`, `psiExtension_map`, `psiExtension_map₂`, `psiExtension_mapComp_hom_combined`, `psiExtension_mapComp_inv_combined` | Existing commutative coefficient and homogeneous-parameter hypotheses; an arbitrary genuine base `TwoSuperfunctor` into the shifted super-opposite | Every integer structure map, combined Q/Π conjugation, canonical extension 1-/2-maps and both full comparison directions are computed with signs and boundary transports. The inverse formula retains the actual base comparison and target whiskering; this does not establish the literal two-sided ψ inverse. |
| Prop 9.4, primary raw evaluation | [BE2] Prop 9.4, proof; (1.11)–(1.12) | `psiPrimaryGen`, `psiPlace_comp`, `psiPrimaryRaw_append`, `psiPrimaryRaw_mem_parity`, `psiPrimaryRaw_mem_degree`, `psiPrimaryRaw_sigma_eq`, `psiPrimaryRaw_mixed_inversion` | Existing commutative coefficient, compatible scalar and homogeneous symmetrizer hypotheses; `t² = −1` for mixed inversion | The four primary shapes are evaluated in actual signed target contexts. Vertical concatenation, both gradings, placement/composition compatibility and distinct-colour mixed inversion are proved. The seven-shape linear evaluator is recorded separately below; the bundled quotient functor remains separate from the complete kernel result below. |
| Prop 9.4, actual same-colour target inversion | [BE2] (1.13)–(1.14), Cor 5.2 and (5.11)–(5.14) | `psiDottedCap_raw`, `psiDottedCup_raw`, `psiSameSigma_eq_composite`, `psiSamePositive_inversion`, `psiSameNegative_inversion`, `psiDiamondCup_zero`, `psiDiamondCap_zero`, `psiDiamondCup_mem_degree`, `psiDiamondCap_mem_degree` | Existing commutative coefficient, compatible scalar and homogeneous symmetrizer hypotheses; `t² = −1` for inversion | All ten actual target matrix blocks, both totalized diamond zeros, parity and integer degrees are proved, including zero weight. Dotted coefficients come from assigned dot powers and genuine normalized whiskering; the crossing is identified with its actual mixed composite. This does not establish contextual descent or the full ψ functor. |
| Prop 9.4, seven-shape free evaluation | [BE2] Prop 9.4; the presentation (1.7)–(1.14) | `psiGen`, `psiRaw_gen`, `psiRaw_append`, `psiRaw_whisk`, `psiDiagram`, `psiLin`, `psiLin_mkD`, `psiLin_comp`, `psiLin_quadEq` | Existing commutative coefficient, compatible scalar and homogeneous symmetrizer hypotheses; `t² = −1` for the relation check | All seven original shapes, their signed contextual placement, both gradings, the original free linear syntax and vertical composition are evaluated. The equal-colour quadratic relation vanishes under this evaluation, including arbitrary linear pre/post composites. The complete presentation-ideal kernel is proved below; quotient Hom descent and the strict graded bare ψ 2-superfunctor are recorded below. |
| Prop 9.4, original derived left cup/cap evaluation | [BE2] Definition 2.2 and Prop 9.4 | `etaPDiagram_lin`, `epsPDiagram_lin`, `psiLin_etaP`, `psiLin_epsP` | Existing commutative coefficient, compatible scalar and homogeneous symmetrizer hypotheses; `t² = −1` | The original two-branch free expressions map to the existing derived left generators, and their seven-shape evaluation equals the computed right-cap/right-cup images at every weight, including zero. Literal source/target transports and coefficients are retained. This is a free-evaluation result, not quotient descent or the full two-sided ψ inverse. |
| Prop 9.4, signed contextual upward-relation checks | [BE2] Definition 1.5 and Prop 9.4 | `psiLin_place`, `psiLin_quadEq`, `psiLin_quadZero`, `psiLin_quadNe`, `psiLin_slideL`, `psiLin_slideR`, `psiLin_slideLEq`, `psiLin_slideREq`, `psiLin_braid`, `psiLin_braidEq` | Existing commutative coefficient, compatible scalar and homogeneous symmetrizer hypotheses; `t² = −1` for relation checks | Original free-linear whiskering and boundary retyping commute with evaluation in arbitrary signed contexts. All nine upward defining-relation cases vanish, including the ordered quadratic polynomial and complete corrected braid; arbitrary signed horizontal and linear vertical contexts are supported. The complete presentation-ideal kernel is proved below; the strict graded bare quotient functor is recorded below. |
| Prop 9.4, inversion-family relation kernels | [BE2] (1.12)–(1.14) and Prop 9.4 | `Rel.IsInversion`, `psiLin_inversion`, `psiLin_inversion_context` | Existing commutative coefficient, compatible scalar and homogeneous symmetrizer hypotheses; `t² = −1` where required by the individual relation | All fourteen original inversion-family constructors evaluate to zero: both unequal-colour equations, ten same-colour matrix relations and both totalized zero-entry relations. The family admits arbitrary linear pre/post compositions. Full signed-context and ideal closure are supplied by the kernel result below; quotient Hom descent is recorded separately below. |
| Prop 9.4, complete presentation-ideal kernel | [BE2] Definition 1.5 and Prop 9.4 | `psiLin_ideal`, `psiLin_homRel` | Existing commutative coefficient, compatible scalar and homogeneous symmetrizer hypotheses; `t² = −1` | All 25 original defining constructors, general source super-interchange, arbitrary compatible coloured horizontal contexts, arbitrary linear pre/post compositions and span closure are handled in the existing presentation ideal. The seven-shape evaluation kills that entire ideal and respects its congruence. Quotient Hom descent is provided by the next row; the strict graded bare 2-superfunctor and both literal inverse-functor equalities are recorded below. |
| Prop 9.4, quotient Hom maps | [BE2] Prop 9.4 and the original presentation | `psiMap₂`, `psiMap₂_lin`, `psiMap₂_diag`, `psiMap₂_id`, `psiMap₂_comp`, `psiMap₂_add`, `psiMap₂_smul`, `psiMap₂_mem_parity`, `psiMap₂_mem_degree` | Existing commutative coefficient, compatible scalar and homogeneous symmetrizer hypotheses; `t² = −1` | Linear maps on arbitrary actual quotient Homs descend through the existing class-map kernel and compute on original diagrams. Identity, vertical composition, addition, scalar multiplication, parity and integer degree are preserved. Horizontal whiskering/coherence and the bundled strict graded bare 2-superfunctor are proved below. Its shifted envelope extension and both literal inverse-functor equalities are recorded below. |
| Prop 9.4, strict graded bare ψ | [BE2] Prop 9.4 proof, before shifted-source extension | `psiStrictCore`, `psiTwo`, `psiTwo_isStrict`, `psiTwo_isGraded` | Existing commutative coefficient, compatible scalar and homogeneous symmetrizer hypotheses; `t² = −1` | The quotient Hom maps form a strict graded 2-superfunctor from the unshifted source to the shifted super-opposite, including both whiskerings and coherence. This is the bare functor, not its shifted-source extension or the literal two-sided inverse. |
| Prop 9.4, inverse parameters and cup/cap roundtrips | [BE2] Prop 9.4 | `psiInverseCScalars`, `psiInverseCScalars_involutive`, `psiMap₂_etaP`, `psiMap₂_epsP`, `psiCup_parameter_roundtrip`, `psiCap_parameter_roundtrip`, `psiCup_parameter_roundtrip_reverse`, `psiCap_parameter_roundtrip_reverse` | Existing commutative coefficient, compatible scalar and homogeneous symmetrizer hypotheses; `t² = −1` | The derived auxiliary-parameter rescaling satisfies the root-shift law and is involutive with the opposite square root. Both orders of the cup/cap roundtrips hold for the quotient maps with the actual Π conjugation and boundary transports, including zero weight. These are generator-level calculations, not a literal inverse functor on all envelope morphisms or its complete composite equalities. |
| Prop 9.4, shifted ψ extension | [BE2] Lemma 9.1 and Prop 9.4 | `psiExtension`, `psiExtension_isGraded`, `twoJ_comp_psiExtension`, `psiExtension_restriction_isStrict`, `psiExtension_map_eq_psiShift`, `psiExtension_map₂_toHom`, `psiExtension_mapComp_hom_eq`, `psiExtension_mapComp_inv_eq` | Existing commutative coefficient, compatible scalar and homogeneous symmetrizer hypotheses; `t² = −1` | The graded extension acts on all integer/parity shifts, with explicit quotient-map conjugation and both composition comparisons. Restriction recovers the complete bare functor and is strict. The shifted extension retains its non-strict comparison data, as distinguished in the source; no strictness of the individual shifted extension is claimed. Both literal inverse-functor equalities are proved below. |
| Prop 9.4, inverse-direction shifted ψ | [BE2] Proposition 9.4 | `psiInverseFunctor`, `psiInverseFunctor_isGraded`, `psiInverseFunctor_map₂_eq`, `psiInverseFunctor_mapComp_hom`, `psiInverseFunctor_mapComp_inv`, `psiInverseFunctor_map_forward`, `psiInverseFunctor_map_reverse` | Existing commutative coefficient, compatible scalar and homogeneous symmetrizer hypotheses; `t² = −1` | A graded 2-superfunctor in the reverse direction, using `-t` and `psiInverseCScalars`, with proved coherence and explicit endpoint-sign correction. Both 1-morphism roundtrips hold for all integer/parity shifts. Composite comparison identities and both literal inverse-functor equalities on arbitrary quotient/envelope morphisms are recorded below. |
| Prop 9.4, all-generator parameter roundtrips | [BE2] Proposition 9.4 | `psiGenerator_parameter_roundtrip`, `psiGenerator_parameter_roundtrip_reverse`, `psiWordReverse_inverse_cupDual`, `psiWordReverse_inverse_capDual`, `psiDCup_parameter_roundtrip`, `psiDCap_parameter_roundtrip` | Existing commutative coefficient, compatible scalar and homogeneous symmetrizer hypotheses; `t² = −1`; arbitrary source weights with their word-boundary equality | Both parameter orders return all seven bare presentation generators under the quotient maps and homogeneous Π conjugation, with endpoint transports retained. Diamond images follow from inverse-matrix relations, including totalized zero ranges and zero weight. The context laws and the inverse-functor identities on arbitrary quotient/envelope morphisms are proved below. |
| Prop 9.4, ψ composite comparison and context laws | [BE2] Proposition 9.4 | `PsiInverseLaws`: `psiForwardInverse_mapComp`, `psiInverseForward_mapComp`, `psiForwardInverse_mapId`, `psiInverseForward_mapId`, `psiForwardInverse_isStrict`, `psiInverseForward_isStrict`, `psiForwardInverse_whiskerLeft`, `psiForwardInverse_whiskerRight`, `psiInverseForward_whiskerLeft`, `psiInverseForward_whiskerRight` | `CommRing k`, `Datum`, homogeneous `Scalars`, `Symmetrizer`, compatible `CScalars`; `t² = −1` | Both complete composition and unit comparisons are endpoint equality isomorphisms at arbitrary integer/parity shifts. Both composites are strict and preserve left/right contexts of arbitrary 2-morphisms. This does not assert strictness of the individual shifted ψ functors. Arbitrary quotient/envelope 2-map roundtrips and both whole-functor equalities are proved in the next row. |
| Prop 9.4, two-sided ψ inverse-functor laws | [BE2] Proposition 9.4, arXiv:1701.04133v2 | `PsiFunctorInverses`: `psiForwardInverse_map₂`, `psiInverseForward_map₂`, `psiExtension_comp_inverse`, `psiInverse_comp_extension` | `CommRing k`, `Datum`, homogeneous `Scalars`, `Symmetrizer`, compatible `CScalars`; `t² = −1`; arbitrary integer/parity shifts and arbitrary 2-morphisms | Both composites equal the identity 2-superfunctor, including composition and unit comparisons. Both 2-map roundtrips hold without a homogeneity premise. The inverse uses the derived `psiInverseCScalars` and `-t`, not a printed inverse formula; no strictness of either individual shifted ψ functor is asserted. |
| Homwise graded Chevalley equivalence and whiskering compatibility | [BE2] §9, prerequisites for Prop 9.3 | `chevHomGradedEquivalence`, `Om_plcL_all`, `chevHomObj_id`, `chevHomObj_comp`, `chevHom_whiskerLeft`, `chevHom_whiskerRight` | `CommRing k`, `Datum`, `Scalars`, `Symmetrizer`, `Scalars.Homogeneous`; arbitrary quotient morphisms | Homwise graded equivalence and both whiskering equations complete |
| Prop 9.3, construction of `ω̃` (via Lemma 9.1) | [BE2] Prop 3.5, Lemma 9.1, Prop 9.3 | `chevalleyTwo` (strict graded `ω : 𝔘(𝔤) → 𝔘(𝔤)^{sop}`), `chevalleyQTwo` (`Q`-envelope), `chevalleyQPiTwo` (`ω̃ : 𝔘_{q,π}(𝔤) → 𝔘_{q,π}(𝔤)^{sop}`), `chevalleyQPiTwo_obj` (`λ ↦ -λ`), `chevalleyQPiTwo_map` (`Qᵐ Πᵃ F ↦ Q⁻ᵐ Πᵃ ω(F)`, so `Eᵢ 1_λ ↦ Fᵢ 1_{-λ}`, `Fᵢ 1_λ ↦ Eᵢ 1_{-λ}`), `chevalleyQPiTwo_mapComp` (comparison sign `(-1)^{ab}`, not strict), `chevalleyQPiTwo_isGraded`, `chevalleyQPiTwo_isLocalTwoSuperequivalence` | `CommRing k`, `Datum`, `Scalars`, `Symmetrizer`, `Scalars.Homogeneous` (the §9 standing assumption (1.31)) | `ω̃` constructed with the printed action on objects and 1-morphisms; graded; all hom functors graded superequivalences, surjective on objects. Invertibility of `ω̃`: next row. 2-morphism signs differ from the display in Remark 9.2 by `(-1)^{a+b}` (conjugation by `(-1)^a` on `Πᵃ F`) |
| Prop 9.3, `ω̃` is an isomorphism (adjoint biequivalence reading) | [BE2] Prop 9.3 | `chevalleyQReverseTwo` (graded inverse `G_q : 𝔘_q(𝔤)^{sop} → 𝔘_q(𝔤)` of `chevalleyQTwo`); `chevalleyQGlobalUnit` (`1 ⟹ ω_q ⋙ G_q`), `chevalleyQGlobalCounit` (`G_q ⋙ ω_q ⟹ 1`), strong and graded, with inverses `chevalleyQGlobalUnitInv`, `chevalleyQGlobalCounitInv` and even degree-zero cancellation isomorphisms (`chevalleyQGlobalUnitCompIso`, `chevalleyQGlobalCounitCompIso`, …); triangle identities for `ω_q`: `chevalleyQForwardTriangleIso`, `chevalleyQReverseTriangleIso` (even, degree zero); `chevalleyQPiReverseTwo` (inverse `G̃` of `ω̃`), `chevalleyQPiGlobalUnit`, `chevalleyQPiGlobalCounit` and their inverses, with even degree-zero cancellation isomorphisms; triangle identities for `ω̃`: `chevalleyQPiForwardTriangleIso`, `chevalleyQPiReverseTriangleIso`; `chevalleyQPiTwo_isAdjointBiequivalence` | `CommRing k`, `Datum`, `Scalars`, `Symmetrizer`, `Scalars.Homogeneous` | Proved in the adjoint biequivalence reading of "isomorphism" chosen by the maintainer in #42: `ω̃` has a graded inverse 2-superfunctor `G̃`, a strong graded unit and counit that are invertible up to even degree-zero modifications, and both triangle identities hold up to even degree-zero modifications (`TwoSuperfunctor.IsAdjointBiequivalence`). A strict inverse (composites equal to identity 2-superfunctors) is not constructed. |
| Prop 9.8, corrected proof | [BE2] Prop 9.8, p. 38; Lemma 9.6; ERRATA [BE2] 4 | `RhoExtension.rhoEnvelope`, `RhoExtension.rhoEnvelope_isGraded`, `RhoInverse.rhoInverse_isGraded`, `RhoFunctorLaws.rhoEnvelope_comp_inverse`, `RhoFunctorLaws.rhoInverse_comp_envelope` | Purely even `CommRing k`; `Datum`, `Scalars`, `Symmetrizer`, `Sc.Homogeneous`; `t² = −1` | Graded isomorphism with the statement's Q/Π images, zero intrinsic F parity, and corrected odd–odd crossing coefficient `+t`. Both whole-functor inverse laws hold for arbitrary shifts and 2-morphisms. General supercommutative coefficients and the following K₀/γ assertion are not included. |

**Relation to Ellis–Lauda.** For `I` an odd singleton, [BE2] is a reformulation of the odd
2-category of A. P. Ellis, A. D. Lauda, *An odd categorification of U_q(sl₂)*, arXiv:1307.7816v2,
and supersedes it here; EL is not formalized separately. One relation needs care. EL's odd
dot-cyclicity relation, (3.15) = Lemma 5.1, (5.5), which BE2 refers to as [EL, (3.1)], compares
a dot on a downward strand defined through the left and through the right adjunction. For
`λ ≠ 0` its right-hand side contains a term `2 · (bubble beside the strand)`, but in the case
`λ = 0` that term is missing. The correct relation at every weight, including `⟨hᵢ,λ⟩ = 0`,
is the one in [BE2] (1.27) and Prop 4.1 (4.3)–(4.4) for odd `i` and `n = 1`: a dot slid around
the leftward cap or cup picks up `(-1)^{⟨hᵢ,λ⟩}` plus twice the odd bubble. This is what is
proved here (`eq_1_27`, from `lemma41_eq3_odd`, `lemma41_eq4_odd`, with `oddBubble_consistent` for the odd
bubble at `⟨hᵢ,λ⟩ = 0`). The correction will be made in a planned revision of the papers.

### [BE2] §§9–10: the covering quantum group (in progress)

Names are in `OddMath.CoveringQuantum`. Conventions are those of [BE2] (its `q` is `q⁻¹` in [CHW1]
and [C]). The `(q, π)`-integers are defined over any commutative ring with a unit `q` and an element
`π`, with `π² = 1` where needed; [BE2] works over `ℚ(q)[π]/(π² - 1)`. Index sets need not be
finite and `I` may have no odd elements.

| Statement | Content | Declarations |
| --- | --- | --- |
| §9 (first paragraph), [CHW1] §1.1 | super Cartan datum: generalized Cartan matrix symmetrized by positive integers `dᵢ`, parity with (1.4); `i · j = dᵢ aᵢⱼ` satisfies [CHW1] (a), (b), (d); bar-consistency (10.2) and its consequence [CHW1] (f); root datum `⟨hᵢ, αⱼ⟩ = aᵢⱼ`, `\|i, λ\|` | `SuperCartanDatum`, `SuperCartanDatum.dot`, `SuperCartanDatum.BarConsistent`, `SuperCartanDatum.even_dot_of_barConsistent`, `RootDatum`, `RootDatum.parl` |
| §9, `[n]_{q,π}`, (9.1) | `(q, π)`-integers for `n ∈ ℤ` as printed, `(q - πq⁻¹)[n] = qⁿ - πⁿq⁻ⁿ`, `[m+n] = πⁿq⁻ⁿ[m] + qᵐ[n]`, `[-n] = -π^{\|n\|}[n]`; (9.1) `bar[n] = π^{n-1}[n] = -π[-n]` | `qpNat`, `qpInt`, `qpNat_mul_sub`, `qpNat_add`, `qpInt_neg`, `qpInt_inv`, `qpInt_inv_eq_neg`, `map_qpInt` |
| §9, factorials and binomials | `[n]!`, `[n r]` (Pascal rule) with `[n r][r]![n-r]! = [n]!`, the second Pascal rule, symmetry, `bar[n r] = π^{r(n-r)}[n r]` (bar invariant for `n` odd) | `qpFact`, `qpBinom`, `qpBinom_mul_qpFact`, `qpBinom_succ_succ'`, `qpBinom_symm`, `qpBinom_inv`, `qpBinom_inv_of_odd` |
| §10, `'f ⊗ 'f`, `r` ([CHW1] §1.4) | the free algebra `'f` with its `ℕ[I]`-grading; for any symmetric bicharacter `χ` the twisted multiplication `(x ⊗ y)(x' ⊗ y') = χ(\|y\|, \|x'\|) xx' ⊗ yy'` (associative, unital) and the algebra map `r` with `r(θᵢ) = θᵢ ⊗ 1 + 1 ⊗ θᵢ`; skew derivations `rᵢ`, `ᵢr` ([CHW1] §1.5); [BE2]'s twist `χ(i, j) = q^{-i·j} π^{\|i\|\|j\|}` | `PreF`, `Bichar`, `PreF.twistedMul`, `PreF.twistedMul_assoc`, `PreF.comul`, `PreF.comul_mul`, `PreF.rDeriv`, `PreF.lDeriv`, `SuperCartanDatum.chi`, `SuperCartanDatum.twistedMul_tmul_tmul` |
| §10, the form ([CHW1] Prop. 1.4.1) | bilinear form with `(θᵢ, θⱼ) = δᵢⱼ / (1 - πᵢqᵢ²)`, `(xy, z) = (x ⊗ y, r(z))`, `(x, yz) = (r(x), y ⊗ z)`, symmetric, weight spaces orthogonal (for any normalization `(θᵢ, θᵢ) = nmᵢ`); radical and `f = 'f / I` ([CHW1]'s definition) | `PreF.form`, `PreF.form_mul_left`, `PreF.form_mul_right`, `PreF.form_comm`, `PreF.form_eq_zero_of_ne`, `PreF.radical`, `PreF.Quotient`, `SuperCartanDatum.form`, `SuperCartanDatum.form_θ_θ`, `SuperCartanDatum.radicalF` |
| §10, `f`, (10.1) | [BE2]'s `f`: generators `θᵢ` and the quantum Serre relations (10.1) as printed | `SuperCartanDatum.serreElt`, `SuperCartanDatum.serreF` |
| §10, [CHW1] Prop. 1.7.3 | the left sides of (10.1) satisfy `rₖ(S) = 0` in `'f`, hence lie in the radical (any normalization, `π² = 1`); so [BE2]'s `f` maps onto [CHW1]'s `'f / I`. Scalar inputs: `[t+1][N, t+1] = [N-t][N, t]`, the `(q, π)`-binomial theorem, `Σₜ (-1)ᵗ π^{t(t-1)/2} q^{t(N-1)} [N, t] = 0` (`N` odd or `π = 1`) | `SuperCartanDatum.rDeriv_serreElt`, `SuperCartanDatum.serreElt_mem_radical`, `SuperCartanDatum.serreToRadical`, `SuperCartanDatum.serreToRadical_surjective`, `qpNat_mul_qpBinom`, `qpBinom_prod`, `alternating_qpBinom_eq_zero`, `PreF.rDeriv_serreWord` |
| §9, (9.2)–(9.4) | `U̇_{q,π}(𝔤)` by generators `1_λ`, `eᵢ1_λ`, `fᵢ1_λ` and relations, over any commutative ring with a unit `q` and an element `π` (encoded as a unital algebra; the unit is adjoined) | `CoveringUDot`, `UDot.Rel`, `UDot.one`, `UDot.E`, `UDot.F`, `UDot.one_mul_one`, `UDot.one_mul_E`, `UDot.E_mul_one`, `UDot.comm_rel`, `UDot.serreE_rel`, `UDot.serreF_rel` |
| §9, (9.5) | divided powers and the `𝓛`-form | `UDot.edp`, `UDot.fdp`, `UDot.lForm`, `UDot.edp_mem_lForm` |
| §9, (9.6), (9.7) | the antilinear automorphisms `ω`, `ψ`, for a bar involution `σ` with `σ(q) = q⁻¹`, `σ(π) = π`, `π² = 1`; both are involutions | `UDot.omega`, `UDot.omega_E`, `UDot.omega_F`, `UDot.omega_smul`, `UDot.omega_omega`, `UDot.psi`, `UDot.psi_F`, `UDot.psi_smul`, `UDot.psi_psi`, `UDot.BarData.map_serreCoeff` |
| §9, (9.8)–(9.10) | linear involutive antiautomorphism `ρ` (`π² = 1`); antilinear antiautomorphisms `∗ = ρ ∘ ψ` and `! = ψ ∘ ρ`, mutually inverse for an involutive scalar bar | `UDot.rho`, `UDot.rho_E`, `UDot.rho_F`, `UDot.rho_rho`, `UDot.star`, `UDot.shriek`, `UDot.star_E`, `UDot.star_F`, `UDot.shriek_E`, `UDot.shriek_F`, `UDot.star_shriek`, `UDot.shriek_star` |
| §9, nonunital algebra underlying (9.2)–(9.4) | the block sum inside the unital envelope, equal to the nonunital algebra generated by the weight and Chevalley generators; finite block decomposition and uniqueness; augmentation excludes the scalar unit for a nontrivial coefficient ring; `ρ`, `ψ`, `∗`, `!` preserve the block sum | `UDot.modified`, `UDot.block`, `UDot.modified_eq_adjoin`, `UDot.mem_modified_iff`, `UDot.exists_localUnit`, `UDot.block_sum_injective`, `UDot.augmentation`, `UDot.unit_not_mem_modified`, `UDot.rho_mem_modified`, `UDot.psi_mem_modified`, `UDot.star_mem_modified`, `UDot.shriek_mem_modified` |
| §10, [CHW1] §1.4, descent of the form | the symmetric form descends to the radical quotient and is nondegenerate there, for any normalization over a commutative ring; this does not identify the radical with the Serre ideal | `PreF.quotientForm`, `PreF.quotientForm_mk`, `PreF.quotientForm_comm`, `PreF.quotientForm_nondegenerate`, `PreF.quotientForm_unique` |
| §10, form on the Serre presentation (exact reduction) | for `π² = 1`, the descended form on `serreF` is symmetric and has the prescribed normalization; its radical is the kernel of `serreToRadical`; nondegeneracy is equivalent to the Serre-ideal equality, proved over the generic covering coefficients below | `SuperCartanDatum.serreForm`, `SuperCartanDatum.serreForm_toSerreF`, `SuperCartanDatum.serreForm_θ_θ`, `SuperCartanDatum.serreForm_radical_iff`, `SuperCartanDatum.serreIdeal`, `SuperCartanDatum.serreForm_nondegenerate_iff_ideal_eq` |
| §9, generic coefficients; §10, normalization denominators | the polynomial quotient `ℚ(q)[π]/(π²-1)`, its `π² = 1`, unit `q`, specializations, and involutive scalar bar; every `1 - πᵢqᵢ²` and its `norm` inverse is a unit | `Coefficients.Ring`, `Coefficients.pi_sq`, `Coefficients.q`, `Coefficients.specialize`, `Coefficients.bar`, `Coefficients.bar_bar`, `Coefficients.barData`, `Coefficients.denominator_isUnit`, `Coefficients.denominator_mul_norm`, `Coefficients.norm_isUnit` |
| §10, ordinary specialization | at `π = 1`, the free form is LieLean's form with parameter `q⁻¹`; quantum Gabber–Kac gives radical = Serre ideal and nondegeneracy for finite index type over a characteristic-zero field with transcendental `q`; the negative-sign and generic results are separate steps below | `SuperCartanDatum.lusztigDatum`, `SuperCartanDatum.form_one`, `SuperCartanDatum.serreElt_one`, `SuperCartanDatum.serreIdeal_one_eq_radical`, `SuperCartanDatum.serreForm_one_nondegenerate` |
| [CFLW] §2.2, twisting inputs (partial) | the ordered form has the required skew part modulo four; for `t² = -1` and bar-consistent data, `q ↦ tq` relates the two bicharacters and normalizations; an invertible diagonal word-basis map is constructed; these modules supply the inputs to the form comparison below | `SuperCartanDatum.twistPhi_skew_mod_four`, `SuperCartanDatum.chi_twist`, `SuperCartanDatum.norm_twist`, `PreF.wordGauge`, `PreF.wordGauge_monomial`, `PreF.wordPhase_append` |
| [CFLW] §2.1, coefficient splitting | the coefficient quotient is isomorphic to the product of its `π = 1` and `π = -1` specializations; equality is detected by the two evaluations; this scalar theorem is used in the half-algebra ideal detection below | `Coefficients.split`, `Coefficients.splitEquiv`, `Coefficients.eq_iff_specialize_eq` |
| §10, twisting comparison of free forms | under bar-consistency and `t² = -1`, the diagonal word map intertwines the free forms at `π = -1` and `π = 1` with parameter `tq`, and identifies their radicals; generic coefficient descent is completed below | `PreF.wordGauge_rDeriv`, `PreF.form_wordGauge`, `SuperCartanDatum.freeTwist`, `SuperCartanDatum.form_freeTwist`, `SuperCartanDatum.freeTwist_mem_radical_iff` |
| §10, twisting of Serre generators | the fourth-root parameter change has an explicit quantum-binomial phase; the diagonal word map sends each ordinary Serre generator to a unit multiple of the corresponding `π = -1` generator under bar-consistency; the entire ideal is transported using diagonal-map invariance | `qpBinom_twist`, `SuperCartanDatum.qpBinom_qi_twist`, `SuperCartanDatum.freeTwist_serreWord`, `SuperCartanDatum.serre_phase_mod_four`, `SuperCartanDatum.freeTwist_serreElt` |
| §10, negative-sign nondegeneracy after scalar extension | for finite index type, bar-consistent data and transcendental `q` over a characteristic-zero field containing a unit `t` with `t² = -1`, the Serre ideal equals the form radical at `π = -1`; no order on the indices is required as an input; descent to the base field is proved below; reconstruction over the generic covering ring follows below | `SuperCartanDatum.serreIdeal_eq_span`, `SuperCartanDatum.wordGauge_mem_serreIdeal`, `SuperCartanDatum.freeTwist_mem_serreIdeal`, `SuperCartanDatum.serreIdeal_neg_one_eq_radical`, `SuperCartanDatum.serreForm_neg_one_nondegenerate` |
| §10, negative-sign nondegeneracy over the base field | for finite bar-consistent data over any characteristic-zero field and transcendental `q`, radical = Serre ideal and nondegeneracy at `π = -1`; no square root of `-1` is assumed in the base field; coefficient transport of forms and faithful tensor inclusion give descent from an algebraic closure; the generic covering-ring theorem follows by the two-sign reconstruction below | `PreF.form_mapCoeffs`, `PreF.mapCoeffs_mem_radical_iff`, `SuperCartanDatum.mapCoeffs_mem_serreIdeal_iff`, `SuperCartanDatum.serreIdeal_neg_one_eq_radical_of_transcendental`, `SuperCartanDatum.serreForm_neg_one_nondegenerate_of_transcendental` |
| §10, generic half-algebra nondegeneracy | for finite bar-consistent Cartan data, the free-form radical equals the Serre ideal over the ring `ℚ(q)[π]/(π²-1)` and the bilinear form on `serreF` is nondegenerate; central idempotents prove that the two specialized ideals detect the generic ideal; this is the half-algebra input, not the form on the modified full algebra of Theorem 10.1 | `SuperCartanDatum.smul_mem_serreIdeal_of_mapCoeffs`, `Coefficients.mem_serreIdeal_iff_specialize`, `Coefficients.serreIdeal_eq_radical`, `Coefficients.serreForm_nondegenerate` |
| §§9–10, half-algebra maps and weight blocks | positive and negative maps from the Serre half algebra to `UDot.modified`, for any commutative coefficient ring, unit `q`, and element `π`; the identity maps to `1_λ`, generators to `eᵢ1_λ` and `fᵢ1_λ`; homogeneous images lie in the prescribed blocks and multiplication has the required weight shift; generic-ring injectivity is proved below | `UDot.positiveHalf`, `UDot.negativeHalf`, `UDot.positiveHalf_θ`, `UDot.negativeHalf_θ`, `UDot.halfBlock`, `UDot.halfMap_mem_block`, `UDot.positiveHalf_mul`, `UDot.negativeHalf_mul` |
| §§9–10, triangular spanning | over any commutative coefficient ring, the modified algebra is the span of matched negative-positive words and of products of the half maps; this proves spanning only, not injectivity, a basis, or the form of Theorem 10.1 | `UDot.triangularSpan_eq_modified`, `UDot.span_normalWords_eq_modified`, `UDot.span_halfProducts_eq_modified` |
| [CHW1] v2 Proposition 2.2.2(b), lowering operators | corrected lowering numerator and mixed generator identity over a commutative ring; operators descend to the Serre half algebra over `ℚ(q)[π]/(π²−1)` for finite bar-consistent data | `UDot.lowerNumerator_θ_mul`, `UDot.GenericVerma.lower`, `UDot.GenericVerma.lower_θ_self` |
| [BE2], positive Serre operator identities | proved on the free half for any commutative ring, unit `q`, and `π² = 1`; hence the descended operators define a positive-half action for finite bar-consistent data over `ℚ(q)[π]/(π²−1)` | `UDot.lowerFree_serre`, `UDot.GenericVerma.lower_serre_sum`, `UDot.GenericVerma.positiveAction` |
| [BE2], highest-weight module weight projections | quotient weight projections, orthogonal idempotents, and homogeneity of both Chevalley operators; finite bar-consistent root datum over `ℚ(q)[π]/(π²−1)` | `UDot.GenericVerma.weightProject`, `UDot.GenericVerma.weightProject_mul`, `UDot.GenericVerma.weightProject_lower`, `UDot.GenericVerma.weightProject_θ_mul` |
| [BE2], normalized mixed relation | the lowering/left-multiplication supercommutator on each quotient weight projection is `[⟨hᵢ, μ⟩]ᵢ`; the free-word identity holds over a commutative ring with unit `q`, `π² = 1`, and unit lowering denominator | `UDot.lowerFree_mixed_monomial`, `UDot.GenericVerma.lower_mixed_project` |
| [BE2], modified highest-weight representation | action of the unital envelope and its nonunital modified subalgebra on the negative Serre quotient, with all idempotent, generator-weight, mixed, and Serre relations; finite bar-consistent root datum over `ℚ(q)[π]/(π²−1)` and arbitrary highest weight; no faithfulness or triangular injectivity claim | `UDot.GenericVerma.freeAction_rel`, `UDot.GenericVerma.representation`, `UDot.GenericVerma.modifiedRepresentation`, `UDot.GenericVerma.representation_one`, `UDot.GenericVerma.representation_E`, `UDot.GenericVerma.representation_F` |
| [CHWII] §4.2 Prop. 4.8 / [Clark IV] §5.2 Prop. 5.8, Verma precursor | symmetric normalized rho-contravariant bilinear form on the existing Serre-half Verma module, for finite bar-consistent general root datum and arbitrary highest weight; constructed from the vacuum coefficient and triangular spanning, not assumed; this is not the integrable quotient | `UDot.GenericVerma.polarization`, `polarization_comm`, `polarization_one_one`, `polarization_vacuum`, `polarization_adjoint` |
| [CHWII] Prop. 6.10, algebraic comparison ingredient in the rho/tau1-prime convention | on arbitrary words, the Verma polarization, normalized by an explicit pi-sign whose square is one, differs from the existing half form by evaluation of a highest-weight-independent polynomial of total degree at most the word length, with zero constant coefficient; parameters are `pi_i^abs(h_i(Lambda)) q_i^(2 h_i(Lambda))`; no valuation, integrable descent, or full nondegeneracy claim | `UDot.GenericVerma.polarization_sub_half`, `wordPolynomial_constantCoeff`, `comparisonError_constantCoeff`, `comparisonError_totalDegree`, `wordSign_sq` |
| [CHWII] Prop. 6.10, q-adic comparison in the rho/tau1-prime convention | proved for arbitrary finite free inputs over a finite bar-consistent root datum, after each `pi = ±1` specialization: an explicit finite-coefficient valuation bound and convergence of the normalized Verma form to the half form at `q = 0`; coordinate-filter nonvacuity is equivalent to existence of a weight with every simple-coroot coordinate positive, not automatic; no integrable descent or modified-form nondegeneracy | `QAdic.eval_order_lower`, `UDot.GenericVerma.normalizedPolarization_order_both`, `normalizedPolarization_tendsto`, `polarization_word_order`, `coordinateFilter_neBot_iff_positive_weight` |
| [CHWII] Remark 2.5 / Prop. 4.8, source-generated quotient in the rho/tau1-prime convention | for finite bar-consistent general root datum and explicit dominant highest weight, integrability powers are proved singular, the submodule they generate lies in both radicals, and the representation and normalized symmetric polarization descend to that exact quotient; arbitrary representatives, explicit E/F adjointness, nonzero highest vector, and normalized half-form polynomial comparison; no local-nilpotence, simplicity, nondegeneracy or tensor J-polarization claim | `UDot.GenericVerma.lower_integrabilityGenerator`, `integrabilityRelations_le_radical`, `integrabilityRelations_le_right_radical`, `integrableRepresentation`, `integrablePolarization`, `integrablePolarization_adjoint`, `integrablePolarization_sub_half` |
| [Clark IV] §2.3 and §5.3 prerequisites | linear Clark omega/inverse and the lowest-weight action on the source-generated quotient; cross-adjointness of the integrable polarization (before J-repair) pairs omega with its inverse; arbitrary involutive characters preserve the relation submodule, yielding quotient Koszul E/F covariance and the existing J/word normalization at both pi signs | `UDot.clarkOmegaEquiv`, `rho_clarkOmega`, `UDot.GenericVerma.lowestRepresentation`, `lowest_cross_adjoint`, `diagonal_integrabilityRelations`, `integrableParity_E`, `integrableParity_F`, `integrableJ_word` |
| Global quotient operators and lowest J-repair | the finite root-image grading descends through the relation submodule; both global Chevalley halves satisfy all single-factor Serre relations, and weight scaling has proved covariance; J intertwines the distinct omega/inverse actions, giving a same-action rho-adjoint lowest bilinear form with vacuum norm one; no independent-root, local-nilpotence, or nondegeneracy assumption | `UDot.GenericVerma.integrableGrading`, `sum_integrableGrading`, `integrableChevalley_serre`, `integrableWeight_chevalley`, `lowest_J_intertwine`, `lowestPolarization_adjoint`, `lowestPolarization_vacuum` |
| Mixed tensor positive-half descent | Delta1/Delta2 positive operators with `v=q^-1`; all positive Serre relations on arbitrary tensors of the highest/lowest quotients for finite bar-consistent root data and arbitrary weights; positive-half action, finite-projector corners and shifted multiplication | `UDot.GenericVerma.tensorE_serre`, `tensorPositiveAction_θ`, `tensorProject_positiveAction`, `tensorPositiveBlock_mul`, `tensorEBlock_serre` |
| Complete Delta1/Delta2 tensor action of the [BE2] §9 presentation | negative operators retain the Clark-omega `pi_i J_i E` factor and the coproduct J/K/Koszul factors; negative Serre and every mixed commutator hold as endomorphism identities on arbitrary tensors, and all relations of the presentation descend to `CoveringUDot` and its nonunital modified algebra. Finite bar-consistent general root datum, generic covering coefficients, arbitrary highest weights; no independent-root or dominance assumption | `UDot.GenericVerma.lowestF_project`, `lowestF_eq_pii_J_E`, `tensorF_serre`, `tensor_mixed_project`, `tensorBlock_comm`, `tensorNegativeBlock_mul`, `tensorFBlock_serre`, `tensorFreeAction_rel`, `tensorRepresentation`, `tensorModifiedRepresentation` |
| Delta1/Delta2 tensor J-polarization, quotient contravariance | product of the accepted highest and J-repaired lowest forms on the quotient tensor for explicit dominant weights; vacuum norm one, symmetry, exact global and weight-labelled E/F adjoints, self-adjoint weight projectors, and contravariance for the full algebra pair the two coproduct actions through rho=tau1-prime at `v=q^-1`; no nondegeneracy, printed tau1/Delta3/Delta4 identification or separation claim | `UDot.GenericVerma.tensorPolarization`, `tensorPolarization_representatives`, `tensorPolarization_vacuum`, `tensorPolarization_symmetric`, `tensorPolarization_global_E`, `tensorPolarization_global_F`, `tensorPolarization_adjoint`, `tensorPolarization_modified_adjoint` |
| Normalized tensor Gram comparison | finite bar-consistent general root datum over the covering ring; coefficient-bar input transports preserve rho-adjointness, and every positive pair or mixed fixed-column pair has a single zero-constant residual polynomial independent of growing dominant weights and both coproducts; no independent-root assumption | `UDot.PolarizationTransport.gram_adjoint`, `modifiedGram`, `UDot.PositiveComparison.actual_positive_residual`, `fixed_column_residual` |
| Cyclic finite-span injectivity | new result (not in the sources); proved over `ℚ(q)[π]/(π²−1)` for finite `I` and bar-consistent root data: every finite set of Serre tensors has one nonnegative bound `B` such that, whenever all coroot coordinates of both weights are at least `B`, both coproduct cyclic maps are injective on its entire covering-ring span; the map is `triangularTensor` followed by `tensorRepresentation` and evaluation on the integrable highest/lowest vacuum; no root independence or freeness hypothesis | `UDot.GenericVerma.NativeCyclic.cyclic`, `cyclic_truncation_injective_bound`, `finite_span_cyclic_injective_bound` |
| Dominant tensor-family joint faithfulness | new result (not in the sources); proved over `ℚ(q)[π]/(π²−1)` for finite `I`, bar-consistent root data and an explicitly given weight `ξ` with `∀ i, 0 < D.h i ξ`: for each fixed coproduct separately, the dominant highest/lowest tensor family jointly detects arbitrary elements of the nonunital modified algebra; the dominant members of `(ζ + n • ξ, n • ξ)` already suffice; not faithfulness of an individual tensor representation or the entire unital envelope | `UDot.GenericVerma.NativeFamily.cofinal_eq_iff`, `dominant_eq_iff`, `dominant_kernel_iff`, `dominant_jointly_injective`, `dominant_point_separating` |
| Normalized mixed-Gram uniform bound and joint limit | after both `pi = ±1` specializations at `q = 0`, one explicit finite-coefficient threshold works for both Delta1/Delta2 choices; the dominant-pair Gram converges to the positive modified form, even for varying coproduct choice; a strictly positive coroot weight is required only for nonvacuity and cofinal sequences | `UDot.NormalizedJointLimit.modifiedGram_order_both`, `gramExtension_eq`, `gramExtension_tendsto`, `nonvacuous_joint_limit`, `cofinalPair_tendsto`, `cofinalPair_gram_tendsto` |
| [BE2], individual half embeddings | the existing positive and negative maps into the nonunital modified algebra have linear left inverses at every right weight; finite bar-consistent root datum over `ℚ(q)[π]/(π²−1)`; this does not prove triangular injectivity or the full modified form | `UDot.negativeRetraction_half`, `UDot.negativeHalf_injective`, `UDot.positiveRetraction_half`, `UDot.positiveHalf_injective` |
| [BE2], matched triangular tensor multiplication | multiplication from the two full Serre halves onto each fixed right column of the modified algebra; homogeneous positive degree determines the intermediate weight; any commutative coefficient ring; generic-ring injectivity is proved below | `UDot.triangularTensor_homogeneous`, `UDot.triangularTensor_θ_θ`, `UDot.range_triangularTensor`, `UDot.triangularColumn_surjective` |
| Regular triangular tensor operators | finite bar-consistent data over `ℚ(q)[π]/(π²−1)`; mixed relation and negative Serre identities hold on the full tensor product, with exact normal-product vacuum evaluation; positive Serre and modified-presentation descent are proved below | `UDot.GenericTensor.positive_negative`, `UDot.GenericTensor.negative_serre`, `UDot.GenericTensor.triangular_vacuum` |
| Regular tensor positive Serre descent | finite bar-consistent data over `ℚ(q)[π]/(π²−1)`, arbitrary integral parameters; positive Serre holds on the full tensor product, yielding a positive-half algebra action and vacuum recovery for arbitrary half elements; modified-presentation descent and triangular injectivity are proved below | `UDot.GenericTensor.toral_positive`, `UDot.GenericTensor.positiveFree_mixed`, `UDot.GenericTensor.positive_serre`, `UDot.GenericTensor.positiveHalfAction_θ`, `UDot.GenericTensor.halfActions_vacuum` |
| Regular tensor representation | finite bar-consistent root datum over `ℚ(q)[π]/(π²−1)`, arbitrary fixed right weight, with no root independence; finite-support weight projectors, full generator covariance, and all defining relations of the modified presentation | `UDot.GenericTensor.weightProject_monomial`, `UDot.GenericTensor.weightProject_positive`, `UDot.GenericTensor.weightProject_negative`, `UDot.GenericTensor.positive_negative_project`, `UDot.GenericTensor.freeAction_rel`, `UDot.GenericTensor.representation` |
| Fixed-column triangular decomposition | over `ℚ(q)[π]/(π²−1)` for finite bar-consistent root data, concrete tensor evaluation is a left inverse to the matched triangular multiplication on every tensor; combining column surjectivity gives a linear equivalence; no full modified-form, integral-form, or canonical-basis assertion | `UDot.GenericTensor.tensorEval_triangularTensor`, `UDot.GenericTensor.triangularTensor_injective`, `UDot.GenericTensor.triangularColumn_injective`, `UDot.GenericTensor.triangularColumnEquiv`, `UDot.GenericTensor.triangularColumnEquiv_symm_apply` |
| Global triangular coordinates | over `ℚ(q)[π]/(π²−1)` for finite bar-consistent root data and arbitrary additive weight group, the nonunital modified algebra is linearly equivalent to finitely supported right-weight tensor families, with explicit column-evaluation inverse and both roundtrips; the existing family of tensor representations jointly separates elements | `UDot.GenericTensor.globalTriangularEquiv`, `UDot.GenericTensor.triangularCoordinates_apply`, `UDot.GenericTensor.triangularTensor_coordinates`, `UDot.GenericTensor.eq_iff_modifiedRepresentation` |
| Theorem 10.1 proof, `σ` | constructed by presentation descent over any commutative ring, unit `q`, and `π² = 1`: involutive linear E/F-swapping antiautomorphism of the nonunital modified algebra; reverses block indices and half words with the correct right-weight shift | `UDot.sigmaFree_rel`, `UDot.sigma_bijective`, `UDot.sigmaModifiedEquiv`, `UDot.sigmaModifiedEquiv_mul`, `UDot.sigma_halfWord` |
| Covering coefficient characters | integral-weight parity characters do not separate coefficients over `ℚ(q)[π]/(π²−1)` | `Coefficients.parity_characters_not_separating` |
| Lusztig 26.1.2 / [C] 5.2, all-half-pairs construction | symmetric bilinear form on the nonunital modified algebra over `ℚ(q)[π]/(π²−1)` for finite bar-consistent data, with both endpoint orthogonality, left `ρ`-adjointness, normalization on every negative-half pair, and uniqueness; no simple-root independence; uses the library's explicit `ρ` and negative-half-form conventions; distinct from the positive-normalized precursor below | `UDot.GenericTensor.negativeColumnFunctional_rho_halfMap`, `UDot.GenericTensor.modifiedForm`, `UDot.GenericTensor.modifiedForm_orthogonal`, `UDot.GenericTensor.modifiedForm_adjoint`, `UDot.GenericTensor.modifiedForm_negativeHalf`, `UDot.GenericTensor.modifiedForm_unique`, `UDot.GenericTensor.modifiedForm_comm` |
| Theorem 10.1, convention-transport boundary | at weight zero, the negative-normalized form has positive norm `πᵢ normᵢ`; for an odd root, its direct psi pullback fails positive normalization and its sigma/psi pullback fails the [BE2] star-adjoint law; finite bar-consistent data over the generic covering ring; these diagnostic candidates are distinct from the constructed form below | `UDot.GenericTensor.rho_adjoint_generator_zero`, `UDot.GenericTensor.psiPullback_positive_generator_zero_ne`, `UDot.GenericTensor.sigmaPsiPullback_not_star_adjoint` |
| Theorem 10.1(1)–(5), construction and all-half characterization | sesquilinear form over `ℚ(q)[π]/(π²−1)` for finite bar-consistent data; the [BE2] star/shriek adjoints, both endpoint orthogonality, positive reversed-word normalization and psi-twisted symmetry; all-half uniqueness needs no root independence; existence without bar consistency remains open; nondegeneracy is proved below (for root data `C.rootDatumOf R`) | `UDot.GenericTensor.sesquilinearForm`, `sesquilinearForm_eq_iff`, `sesquilinearForm_reversed_words`, `sesquilinearForm_psi_comm`, `sesquilinearForm_shriek_adjoint` |
| Theorem 10.1, bounded mixed nondegeneracy | the positive bilinear and BE2 sesquilinear forms are nondegenerate on `span {1_{−αᵢ}, qᵢFᵢEᵢ1_{−αᵢ}}` for each simple root, over the generic covering ring with finite bar-consistent data; unit mixed Gram pivot; no root independence; nondegeneracy of both forms on the whole modified algebra is proved below (row "Theorem 10.1, nondegeneracy (proved)", for root data `C.rootDatumOf R`) | `UDot.GenericTensor.positiveModifiedForm_mixedPlane_nondegenerate`, `sesquilinearForm_mixedPlane_nondegenerate`, `positiveModifiedForm_mixedPivot_detect` |
| Theorem 10.1, general finite-coordinate recurrence | positive-form pairing recurrence removes one negative generator with a unit prefactor; the full normal-order correction lowers negative word degree on arbitrary finite triangular families; finite bar-consistent data over the generic covering ring, no root independence; this is not full-form nondegeneracy or a valuation theorem | `UDot.GenericTensor.positiveModifiedForm_F_eq_zero_iff`, `coordinateAction_E_leading`, `finiteFamily_E_leading` |
| Theorem 10.1(1)–(3), shorter characterization | same construction hypotheses; same-length reversed-word normalization suffices under the explicit local assumption that equal positive root sums have equal word lengths | `UDot.GenericTensor.sesquilinearForm_eq_iff_of_length_separation` |
| Theorem 10.1 proof, uniqueness over any coefficient ring | two left `ρ`-adjoint bilinear maps on the modified algebra, with values in any module, over any commutative ring with unit `q` and `π² = 1`, agree once they agree on pairs of positive words; root coordinates `μ = rep(μ) + Σ nⱼαⱼ` on the weight lattice when the simple roots are `ℤ`-independent; supporting material only, not nondegeneracy | `UDot.forms_eq_of_positiveWord`, `UDot.positiveWord`, `RootDatum.rootCoord`, `RootDatum.rootCoord_add_α`, `RootDatum.h_eq_rootCosetRep_add_sum` |
| Theorem 10.1 proof, base change | over any commutative ring map `k → k'` sending `(q, π)` to `(q', π')`: the presentation of `U̇` maps relation by relation, `k' ⊗ U̇_{q,π} ≅ U̇_{q',π'}`, and for flat `k'` the same on modified algebras; bilinear forms on the modified algebra extend with block orthogonality, `ρ`-adjointness and positive-word values; over a field extension trivial left radical ascends and descends; over `ℚ(q)[π]/(π²−1)` a form has trivial left radical once both specializations `π = ±1` do; supporting material only, not nondegeneracy | `UDot.mapCoeffs`, `UDot.baseChangeEquiv`, `UDot.modifiedBaseChange`, `UDot.baseChangeForm`, `UDot.baseChangeForm_adjoint`, `UDot.leftRadical_trivial_of_baseChangeForm`, `UDot.baseChangeForm_leftRadical_trivial`, `Coefficients.leftRadical_trivial_of_specialize` |
| Theorem 10.1 proof, twistor of `U̇` | for bar-consistent data, an order on `I`, `t² = −1` and integer root coordinates of the weights: rescaling `eᵢ1_λ`, `fᵢ1_λ` by explicit signs and powers of `t` is an algebra isomorphism `U̇_{q,−1} ≅ U̇_{tq,1}` fixing every `1_λ`; it commutes with `ρ`, and rescales positive words compatibly with the free half-algebra forms at the two signs; general rescaling criterion for the presentation (9.2)–(9.4); supporting material only, not nondegeneracy | `UDot.gauge`, `UDot.GaugeCompatible`, `UDot.twistor`, `UDot.twistorAdjoint_eq`, `UDot.rho_twistor`, `UDot.qpInt_twist`, `UDot.form_twist_monomial` |
| Theorem 10.1, nondegeneracy reduced to `π = 1` | for finite bar-consistent data with `ℤ`-independent simple roots, the positive form and the [BE2] sesquilinear form on the modified algebra over `ℚ(q)[π]/(π²−1)` have trivial left radical, **assuming** the `π = 1` input `PositiveFormNondegenerate` over `L = ℚ(q)‾` at the parameters `q` and `tq` (`t² = −1`): every `ρ`-adjoint form on `U̇_{q',1}` with the standard positive-word values is nondegenerate. The input is discharged in the next row from Lusztig's form on `U̇` ([Lus] 26.3.1); independence of the simple roots is part of [BE2] §1's setting | `UDot.PositiveFormNondegenerate`, `UDot.positiveFormNondegenerate_neg_one_of_twist`, `UDot.positiveModifiedForm_leftRadical_trivial`, `UDot.positiveModifiedForm_leftRadical_trivial_algebraicClosure`, `UDot.sesquilinearForm_leftRadical_trivial` |
| Theorem 10.1, nondegeneracy (proved) | for finite bar-consistent data `C.rootDatumOf R` (weights `Hom(Y, ℤ)` of a LieLean root datum `R` with `Y` free of finite rank) with linearly independent simple roots and simple coroots, the positive form and the [BE2] sesquilinear form on the modified covering algebra over `ℚ(q)[π]/(π²−1)` are nondegenerate. Route: at `π = 1` the modified covering algebra is Lusztig's `U̇` at `v = q⁻¹` and the form is the pullback of Lusztig's form, which is nondegenerate by LieLean's [Lus] 26.3.1; `π = −1` reduces to `π = 1` by the twistor. Restrictions relative to [BE2]: the root datum has the shape `C.rootDatumOf R`, and bar-consistency (needed for the construction of the forms) | `UDot.positiveModifiedForm_nondegenerate`, `UDot.sesquilinearForm_nondegenerate`, `exists_dominant_ge_of_linearIndependent_coroot`, `SuperCartanDatum.rootDatumOf`, `UDot.toLusztig`, `UDot.toLusztig_injective`, `UDot.toLusztig_surjective`, `UDot.positiveFormNondegenerate_of_lusztig`, `UDot.positiveFormNondegenerate_of_ratFunc` |
| Theorem 10.3, Claim 1, algebraic positive-word step; ERRATA [BE2] 5 | Proved equal-length weighted-permutation evaluation and unequal-length vanishing of the existing form, with source-to-target indexing, including empty words and repeated colours. Free form: commutative ring, symmetric bicharacter, arbitrary norms; no finite-I assumption. Existing modified-form consumer: finite bar-consistent root datum at a common weight. Rational mixed-index diagnostic proved; the canonical-family Laurent coefficient comparison is proved below. The finite-label comparison at arbitrary certified points is below; mixed-word cases remain open | `PreF.form_monomial_permutations`, `UDot.GenericTensor.sesquilinearForm_positive_words_permutations`, `UDot.GenericTensor.sesquilinearForm_positive_words_eq_zero_of_length_ne`, `PreF.PermutationIndex.form_ne_printed` |
| Theorem 10.3, Claim 1, finite positive matchings and crossing layers | Proved endpoint-equivalence extraction and realization, unequal-length nonexistence, and unique representative/permutation equivalence. Strictly reduced positive matchings are crossing-only and admit ordinary layers mapping exactly to their existing extended layers, with endpoints preserved. Arbitrary colours; representative coverage and uniqueness explicit, finiteness derived. No Cartan, coefficient, finite-I or bar-consistency hypothesis. Weighted degree/parity and canonical dot-series comparison are proved below | `OddMath.SKM.positive_pairing_equiv`, `OddMath.SKM.exists_positive_pairing`, `OddMath.SKM.IsMatching₂.positive_length_eq`, `OddMath.SKM.positive_representatives_equiv`, `OddMath.SKM.IsMatching₂.positive_crossing_moves`, `OddMath.SKM.positive_tLay_ofL` |
| Theorem 10.3, Claim 1, crossing degree and parity | Proved the colour-weighted inversion sums for the existing diagram degree and extended-layer parity of strictly reduced positive matchings, with exact layers and endpoints preserved. Arbitrary `Datum` and symmetrizer; no finite-colour or bar-consistency hypothesis. Physical left-to-right source-to-target indexing; decorated grading and the canonical-family form comparison are proved below | `OddMath.SKM.positive_matching_degree_parity` |
| Theorem 10.3, Claim 1, finite dot decorations | Proved bijective top-endpoint placement for positive strands, canonical decorations in the existing family, injectivity of finite strand counts into existing layer lists, and additive generator degree/parity increments. Arbitrary colours and datum; the count domain is finite, not the space of counts. Canonical top-point choice only; numeric arbitrary-point invariance and canonical-family form comparison are proved below. Arbitrary-selector enumeration remains open | `OddMath.SKM.positive_top_points`, `OddMath.SKM.topDotMoves_family`, `OddMath.SKM.dLay_topDotMoves_injective`, `OddMath.SKM.topDotMoves_degree`, `OddMath.SKM.topDotMoves_parity` |
| Theorem 10.3, Claim 1, formal dot factors | Proved geometric factors and finite-antidiagonal coefficients for finite words, retaining separate counts for repeated colours. Any commutative coefficient ring; no finite-colour or bar-consistency hypothesis. This module identifies the norm by polynomial evaluation. Canonical-family identification and Laurent shifts are proved below; full Claim 1 remains open | `SuperCartanDatum.dotSeries_eq_prod_inverse`, `SuperCartanDatum.coeff_dotSeries`, `SuperCartanDatum.dotCount_monomial`, `SuperCartanDatum.norm_eq_inverse_eval_dotDenominator` |
| Theorem 10.3, Claim 2, algebraic coefficient shift | Proved upward-generator adjointness and the formal Laurent coefficient shift, with no parity factor. The physical left-cons bridge now uses arbitrary existing signed words in unchanged order, with an explicit endpoint-weight condition; the positive specialization retains its scalar reversal convention. Finite colours and bar consistency remain explicit. Right-cup family coefficients are proved below; coefficientwise Claim 2 is proved below under the form restrictions | `UDot.GenericTensor.sesquilinearForm_E_bent_coeff`, `sesquilinearForm_mixed_up_leftCons_bent_coeff`, `sesquilinearForm_positive_leftCons_bent_coeff` |
| Theorem 10.3, decorated representative numerical comparison | Proved degree/parity independence for independently chosen valid strand points and serializers on crossing-minimal matching representatives, with endpoint-preserving colour/label transport. Proved the normalized decorated right-cup degree shift and unchanged parity; bounded source points are explicit for literal transport. Right-cup family coefficients are proved below; coefficientwise Claim 2 is proved below under the form restrictions | `matchingStrandEquivOfIso`, `mixed_decorated_degree_parity_of_iso`, `cupAttach_normalized_decorated_degree_parity` |
| Theorem 10.3, reduced representative numerical comparison | Proved equality of generator-table degree and parity for same-boundary matching representatives with equal pairing and crossing-minimality (`Reduced₂`); no critical-point bound is required. Proved the undecorated normalized right-cup comparison. No scalar, span, nonzero-morphism or assumed grading premise; decorated comparison is proved above; right-cup family coefficients are proved below; left-cup coefficients are proved below | `numericTPush`, `numericTProcess`, `reduced₂_degree_parity_of_iso`, `cupAttach_normalized_degree_parity` |
| Theorem 10.3, Claim 3, algebraic coefficient shift | Proved the downward star-adjoint coefficient shift including its π factor and correct F/E right idempotents. The physical corollary uses existing mixed words in unchanged order with their endpoint-weight condition. Finite colours and bar consistency remain explicit; literal and normalized left-cup numerical transport is proved below; left-cup family coefficients are proved below; coefficientwise Claim 3 is proved below under the form restrictions | `UDot.GenericTensor.sesquilinearForm_F_bent_coeff`, `sesquilinearForm_mixed_down_leftCons_bent_coeff`, `mixed_word_physical_weight` |
| Theorem 10.3, Claim 3, literal and normalized left cup | Proved matching, endpoint-strand, bounded-point and decoration transport for downward left-cons bending, preservation of crossing-minimality, and degree/parity shifts dᵢ(1−hᵢν) and `ipar D i ν` at the cup-region weight. Independent valid serializers on a chosen reduced target have the same shifts. Arbitrary colours and datum; no assumed grading or strict critical-point preservation. The left cup is anchored to its derived source expressions; left-cup family coefficients are proved below; coefficientwise Claim 3 is proved below under the form restrictions | `cup_attach_down_decorated`, `leftCupAttach_etaP_source`, `reduced₂_leftCupAttach`, `leftCupAttach_root_degree_parity`, `leftCupAttach_normalized_decorated_degree_parity` |
| Theorem 10.3, mixed finite degree fibres | Proved representative finiteness from endpoint-pairing uniqueness and degree-fibre finiteness from positive strand-dot weights. Arbitrary colours; no coverage, reducedness, root independence or assumed finiteness. Ordinary source branches realize the table degree, with scalar anchors for derived cups/caps, not a scalar-free global morphism equality | `matching_representatives_finite`, `mixed_labelled_degree_finite`, `mixed_labelled_source_degree_finite` |
| Theorem 10.3, Claim 2, graphical coefficients | Proved the strand-labelled right-cup equivalence and coefficient shift with both finite fibres derived. Complete unique strictly reduced families and independent valid serializers are explicit; equivalence precedes data/weights, and finite witnesses precede signs/degrees. Arbitrary colours and rational parity specialization; no assumed grading, enumeration or form equality. The coefficientwise form iff is proved below | `strandLabelledEquiv`, `rightCup_labelled_family_coefficients` |
| Theorem 10.3, Claim 2, coefficientwise form equivalence | Proved the right-cup iff comparing every integer Laurent coefficient of the existing mixed-word form to the finite strand-label parity sums, at both signs. Equivalence, finite fibres and both transports are derived; endpoint mismatch is handled by matching conservation and form orthogonality, so no endpoint-weight premise remains. Independent fixed points/serializers, complete unique strictly reduced families, finite colours, bar consistency, additive weights and purely-even coefficients remain explicit. This is not the full Theorem 10.3 or a full-series construction | `rightCup_labelled_form_coeff_iff` |
| Theorem 10.3, Claim 3, graphical coefficients | Proved the left-cup strand-labelled equivalence, finite degree fibres and coefficient shift including the parity factor at square-one rational signs. Complete unique strictly reduced families and independent serializers are explicit. An all-count odd example distinguishes source −1 from target +1 at negative sign; omitting the factor is false. The coefficientwise form iff is proved below | `parity_pow_add`, `leftCup_labelled_family_coefficients` |
| Theorem 10.3, Claim 3, coefficientwise form equivalence | Proved the left-cup iff comparing every integer Laurent coefficient of the existing mixed-word form to finite strand-label parity sums, at both signs. The parity factor is retained and cancelled only after proving it nonzero. Endpoint mismatch is handled by matching conservation and form orthogonality; no endpoint-weight premise remains. Independent points/serializers with bounded source heights, complete unique strictly reduced families, finite colours, bar consistency, additive weights and purely-even coefficients remain explicit. This is not the full Theorem 10.3 or a full-series construction | `leftCup_labelled_form_coeff_iff` |
| Theorem 10.3, Claim 4, boundary-crossing normalization | Proved unchanged degree and parity shift `parity i * parity j` between reduced empty-target matchings with adjacent unequal-colour opposite-oriented boundary strands exchanged. Both intersection cases are covered using planar equivalence of minimal diagrams; no general Reidemeister-II invariance or reducedness of raw attachment is assumed. Arbitrary datum, symmetrizer and additive weights. Distinct odd-colour consumers include both cases and certified finite-label nonzero dots. Representative-family and coefficient transport are proved below | `reduced₂_opposite_boundary_degree_parity`, `canon_opposite_boundary_degree_parity` |
| Theorem 10.3, Claim 4, graphical coefficients | Constructed complete-representative and endpoint-transposition strand equivalences, proved colour preservation, and lifted all natural strand counts by inverse precomposition. Independent valid points/serializers precede grading data; both finite degree fibres and the signed coefficient transport are derived. Arbitrary colours and datum. Both intersection cases have populated finite-label consumers | `boundary_swap_representatives_equiv`, `matchingStrandEquivOfSwap`, `opposite_boundary_labelled_family_coefficients` |
| Theorem 10.3, Claim 4, coefficientwise form equivalence | Proved the distinct-colour iff for all integer Laurent coefficients of the existing contextual mixed-word form and finite strand-label sums at both signs, retaining the parity factor with no endpoint premise. Complete unique strictly reduced families, independent valid points/serializers, finite colours, bar consistency, additive weights, decidable equalities and purely-even coefficients remain explicit. Bar-consistent two-odd-root consumers rederive their populated fibres. This is not the full-series identity or all of Theorem 10.3 | `opposite_boundary_labelled_form_coeff_iff`, `GenericTensor.sesquilinearForm_context_EF_ne_coeff` |
| Theorem 10.3, Claim 5, algebraic commutator; ERRATA [BE2] 6 | Proved the same-colour contextual form difference with the barred quantum integer at the physical suffix endpoint. Finite colours, bar consistency, additive weights, decidable equalities and purely-even coefficients remain explicit. Nonempty-context consumers and an odd weight-two counterexample distinguish the printed unbarred scalar. Graphical three-class cancellation and full Claim 5 remain open | `GenericTensor.sesquilinearForm_context_EF`, `ContextualCommutatorExamples.odd_context_commutator`, `ContextualCommutatorExamples.odd_unbarred_commutator_false` |
| Theorem 10.3, Claims 2–3, endpoint support | Proved matching weight conservation without root independence, actual mixed-word block membership, and vanishing of both matching-family sums and the existing form off endpoint support. The form retains finite-colour and bar-consistency restrictions | `IsMatching₂.wt_eq`, `matching_labelled_finite_sum_eq_zero_of_weight_ne`, `GenericVerma.MixedGram.algebraWord_mem_block`, `GenericTensor.sesquilinearForm_mixed_eq_zero_of_weight_ne` |
| Theorem 10.3, mixed matching numerical transport | Proved the cap-push existential with fit, pairing and crossing bounds, and degree/parity equality when the bound is sharp; strictly decreasing branches do not assert invariance. Proved mixed-matching point-colour transport through cap renaming and exact finite strand-labelled dot contributions, including downward dots. No reducedness or assumed numerical-preservation premise for the dot identity; the undecorated comparison is proved above; right-cup family coefficients are proved below; coefficientwise Claim 2 is proved below under the form restrictions | `numericCapPush`, `onStrand₂_colour`, `mixed_decorated_degree_parity` |
| Theorem 10.3, crossing-minimal cup attachment | Proved preservation of `Reduced₂` and actual crossing count under literal right-cup attachment; arbitrary matching with crossing-minimality, no critical-point bound. A cap-to-zigzag example shows why `StrictReduced₂` is not asserted | `OddMath.SKM.reduced₂_cupAttach`, `ncr₂_cupAttachMatching` |
| Theorem 10.3, one-sided numerical rewrite invariance | Proved generator-table degree and actual parity invariance for all six existing `Chord.Step` constructors, contextual `Rw` and `Chord.Equiv`, with fitting moves. Arbitrary orientations, colours and weights. The table agrees with ordinary `Diagram.degree` and the source left-cup/cap expressions. Cap-push is covered by the numerical transport result above; undecorated reduced comparison is proved above; numerical decorated comparison and right-cup family coefficients are proved above; left-cup coefficients are proved below | `OddMath.SKM.tableDegree_xpar_step`, `tableDegree_xpar_rw`, `tableDegree_xpar_equiv`, `tableDegree_diagram`, `tableDegree_etaP_source`, `tableDegree_epsP_source` |
| Theorem 10.3, Claim 2, literal cup attachment | Proved matching and pairing transport, an endpoint-preserving strand equivalence, bounded distinguished-point and decoration transport, an exact ordinary-layer realization, and the source cup degree shift with unchanged parity. Arbitrary matching and bounded strand points; ordinary input realization explicit. No reducedness of the raw attachment or normalized-family invariance asserted | `OddMath.SKM.cup_attach_up_decorated`, `cup_attach_up_degree_parity`, `onStrand₂_cupAttach`, `decorates₂_cupAttach` |
| Theorem 10.3, Claims 2–3, undecorated boundary correspondence | Proved strictly reduced realization on the bent boundary, pairing-preserving equivalence of representative families with explicit coverage and uniqueness, and existing-layer consumers. Both orientations and arbitrary colours. Literal right-cup dot and grading transport is proved above; undecorated normalized comparison is proved above; decorated right-cup comparison is proved above; literal and normalized left-cup transport is proved above; full Claims 2–3 remain open | `OddMath.SKM.exists_strictReduced_bend`, `OddMath.SKM.bending_representatives_equiv`, `OddMath.SKM.exists_bent_matching_layers` |
| Theorem 10.3, Claim 1, decorated degree and parity | Proved a valid top-point strand equivalence and, for every top-indexed dot count, one existing ordinary diagram with degree/parity equal to source-indexed crossing inversions plus top-dot contributions. Arbitrary datum and symmetrizer; no finite-colour or enumeration premise. The canonical and finite-label coefficientwise form comparisons are proved below; mixed-word geometric invariance remains open | `OddMath.SKM.positive_decorated_degree_parity` |
| Theorem 10.3, Claim 1, covering/diagrammatic datum compatibility | Proved a fieldwise adapter preserving weights, roots, coroots and parity, with crossing degree `−Q.dot` and dot degree `2*Q.d`; applied to the existing matching-degree formula. No finite-colour or bar-consistency hypothesis for this adapter; existing form restrictions are unchanged. Used by the canonical-family form comparison below | `CoveringQuantum.RootDatum.toSKM`, `CoveringQuantum.RootDatum.skmSymmetrizer`, `OddMath.SKM.positive_matching_covering_degree_parity` |
| Theorem 10.3, Claim 1, canonical decorated enumeration | Proved joint syntactic injectivity and an equivalence from colour-preserving permutations and finite top-count vectors to the existing canonical decorated family. Explicit representative coverage/uniqueness and certified top points; no quotient-morphism injectivity or arbitrary-selector/point invariance claimed | `OddMath.SKM.positive_topDotMoves_joint_injective`, `OddMath.SKM.positive_decorated_enumeration` |
| Theorem 10.3, Claim 1, one matching coefficient | Proved finite fibers of the existing integer diagram degree and their parity-weighted coefficient formula, with guarded negative crossing shift. Root datum, commutative coefficient ring and `π²=1`; canonical top points chosen before all counts. The canonical representative sum and its form comparison are proved below; arbitrary-choice comparison remains open | `OddMath.SKM.positive_decorated_coeff` |
| Theorem 10.3, Claim 1, canonical-family coefficients | Proved finite fibers of existing ordinary diagram degree on the canonical decorated family and the guarded colour-compatible permutation coefficient sum. Explicit representative coverage/uniqueness, certified shared placements, commutative ring and `π²=1`. The form comparison at either π sign is proved below; arbitrary-selector/geometric comparison remains open | `OddMath.SKM.positive_decorated_family_coeff` |
| Theorem 10.3, Claim 1, canonical-family form coefficients | Proved that each finite parity-weighted degree fiber of the canonical decorated family equals the Laurent coefficient of the existing modified form after either π-sign specialization. Positive words of arbitrary boundary lengths at a common weight; finite bar-consistent root datum, explicit representative coverage/uniqueness and certified top points. Formal rational-function expansion, with guarded negative shifts; no numerical q evaluation. Unequal lengths give empty graphical families and zero form coefficients, without root independence. The finite-label comparison at arbitrary certified points is below; mixed words and arbitrary raw-selector range comparisons remain open | `UDot.GenericTensor.sesquilinearForm_positive_words_coeff`, `OddMath.SKM.positive_decorated_family_form_coeff` |
| Theorem 10.3, Claim 1, strand-labelled form coefficients | Proved finite actual-degree fibers and their parity-weighted equality with the existing modified-form Laurent coefficients, for arbitrary certified strand points and fixed valid serializers. Positive boundaries of arbitrary lengths; finite bar-consistent root datum, common weight, explicit representative coverage and uniqueness. Ordinary realizations precede all signs and degrees. The index is one representative and one natural-number label per strand; the raw selector API is unchanged. At bounded points the serializer is constructed, not assumed; it and the ordinary realizations precede every sign and degree. Mixed words and arbitrary raw-range enumeration remain open | `OddMath.SKM.positive_labelled_family_form_coeff`, `OddMath.SKM.positive_bounded_points_family_form_coeff` |
| Theorem 10.3, Claim 1, bounded point serialization | Proved existence of a valid existing decorated move list for every finite strand-count vector at bounded certified points. Arbitrary colours, no matching, reducedness, positivity or point-injectivity premise; no grading or coefficient identity assumed | `OddMath.SKM.exists_tmoves_dotPts_perm`, `OddMath.SKM.exists_decorates₂_of_bounded_points` |
| Theorem 10.3, positive distinguished-point grading | Proved existing degree/parity formulas for every valid decoration at arbitrary strand points and dot orders, with the same ordinary layers. Arbitrary datum/symmetrizer; valid decoration and certified strand points explicit. Numeric positive invariance only, not arbitrary-selector enumeration, mixed cup/cap invariance or quotient injectivity | `OddMath.SKM.positive_point_decorated_degree_parity` |
| Highest-weight quotient local nilpotence | both Chevalley halves are locally nilpotent on every vector of the action-generated quotient, over the generic covering ring for finite bar-consistent root data and arbitrary highest weight; raising has formal word-length bounds and lowering follows from the monic Serre relation; no dominance, root independence, field/domain, or nondegeneracy assumption | `UDot.GenericVerma.NativeLeading.integrableChevalley_true_locally_nilpotent`, `UDot.GenericVerma.integrableChevalley_false_locally_nilpotent`, `UDot.GenericVerma.serre_nilpotence_bound` |
| Mixed tensor E/F local nilpotence | proved over the generic covering ring for finite `I`, bar-consistent root data and arbitrary weights and tensor vectors, for both Delta1/Delta2 coproduct choices | `UDot.GenericVerma.tensorE_locally_nilpotent`, `UDot.GenericVerma.tensorF_locally_nilpotent` |

Cross-Delta1/Delta2 tensor J-adjointness and the normalized mixed-Gram joint limit
are proved in the rho=tau1-prime convention. Identification with the printed
tau1/Delta3/Delta4 pairing remains open (modified-form nondegeneracy is proved by the twistor route above).
Joint faithfulness of the dominant tensor family is proved for each fixed coproduct
under an explicitly given strictly positive coroot weight. Cyclic finite-span injectivity
is conditional on the stated coroot bounds; neither result asserts cofinal dominant weights for
arbitrary root data. These results are not used by the nondegeneracy proof above.

## Building

Requires [elan](https://github.com/leanprover/elan). Toolchain `leanprover/lean4:v4.34.1` and Mathlib
`v4.34.1` (`d13f23b723b8a846827a245b89c10fc7d3f11612`) are pinned. The diagrammatic modules depend on
string-diagrams-lean at `4540cd4a47cf0c4d8ef7597cdc8a5fa95c84a11f`, the [EQ] dg structures on
[dg-lean](https://github.com/apellis/dg-lean) at `fe555b543a8a4ab084a6eafef9159dda8339d2fd`, and the
[BE2] Cartan data on [lie-lean](https://github.com/apellis/lie-lean) at
`84222f8a9861e73db9778092c6a9d51ff39315cb` (see `lakefile.lean` and `lake-manifest.json`).

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
