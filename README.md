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
  (in progress).

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
  `EQFix.TriangularBasis.finiteCellFiltration`): `Z_n` over `OΛ_n` (Prop 3.16 (1), `EQFix.znFiniteCellFiltration`,
  `zn_isKProjective_osym`) and `Z_{a,b}` over `OΛ_{a+b}` with `binom(a+b,b)` cells (Cor 4.8, `EQFix.zabFiniteCellFiltration`,
  `zab_hasLiftingProperty`), and the dual bimodule `Z^∨_{a,b}` over `OΛ_{a+b}` (Cor 4.11, `EQFunctor.zdualFiniteCellFiltration`,
  `zdual_isKProjective`), built from a generic graded dual `EQFunctor.RightDual A M = HOM_A(M, A)` of a right dg module
  (a dg `(A, B)`-bimodule for a dg `(B, A)`-bimodule `M`; the dual of a finite triangular right basis is a triangular
  left basis, `RightBasis.dualTriangular`).
- §4.4, Definitions 4.14 and 4.15 on `ℤ`-graded derived categories (`Frontier.EQFunctor*`; `OΛ_a ⊗ OΛ_b` is the dg subring
  `EQFunctor.osymABDG a b` of `OPol_{a+b}`): the multiplication functor `I_{a,b} = Z^∨_{a,b} ⊗^L_{OΛ_a ⊗ OΛ_b} (−)`
  (`EQFunctor.mult`, via the derived tensor product with a dg bimodule over dg rings, `bimoduleDerivedTensor`) and the
  comultiplication functor `R_{a,b}`, derived induction along `OΛ_{a+b} ⊆ OΛ_a ⊗ OΛ_b` (`EQFunctor.comult`, left adjoint to
  restriction, `comultAdjunction`), both triangulated and preserving compact objects; `I_{a,b}(OΛ_a ⊗ OΛ_b) ≅ Z^∨_{a,b}`
  and `R_{a,b}(OΛ_{a+b}) ≅ OΛ_a ⊗ OΛ_b` (`multSelfIso`, `comultSelfIso`); on `K₀`,
  `[I_{a,b}(OΛ_a ⊗ OΛ_b)] = Σ_{μ ∈ Par(b,a)} (−1)^{|μ|} [OΛ_{a+b}]` and `[R_{a,b}(OΛ_{a+b})] = [OΛ_a ⊗ OΛ_b]`
  (`K0Mult_self`, `K0Comult_self`), the `ℤ`-graded form of the two computations in the proof of Thm 4.17. Def 4.18
  for `N ≥ 2` (`Frontier.EQFunctorEmbedding`): `J_N = Z_N^∨ ⊗^L_{ONH_N} (−) : D(ONH_N) → D(OΛ_N)` (`EQFunctor.J`, with
  `Z_N^∨` finite-cell over `OΛ_N`, `znDual_isKProjective`), fully faithful since `D(ONH_N) = 0` (Cor 4.19 for `N ≥ 2`,
  `jFullyFaithful`); for `N ≤ 1` (`Frontier.EQFunctorEmbeddingSmall`, `ONH_N = OPol_N`) `J_N` is an equivalence, since
  `Z_N^∨ ≅ OΛ_N` and `J_N ≅` derived induction along the isomorphism `OPol_N ≅ OΛ_N` (`jSmall_isEquivalence`,
  `jSmallFullyFaithful`; generic `bimoduleDerivedTensorIsoInduction`), so Cor 4.19 holds in every rank. The `⊠` form of
  Def 4.14 (`Frontier.EQFunctorBox`): `I_{a,b}(M, N) = Z^∨_{a,b} ⊗^L_{OΛ_{a,b}} (M ⊠ N)` with dg-lean's derived external
  tensor product transported along `OΛ_a ⊗ OΛ_b ≅ OΛ_{a,b}` (`EQFunctor.multBox`), `I_{a,b}(OΛ_a, OΛ_b) ≅ Z^∨_{a,b}`
  (`multBoxSelfIso`), and its symbol `[M] ⊗ [N] ↦ [I_{a,b}(M, N)]` with
  `[I_{a,b}(OΛ_a, OΛ_b)] = Σ_{μ ∈ Par(b,a)} (-1)^{|μ|} [OΛ_{a+b}]` (`K0MultBox_mk`, `K0MultBox_self`).
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
  dg rings induced by `K ⊗ (OΛ_{a+b} ⊆ OΛ_{a,b})`; its symbol followed by Lemma 4.16 sends
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
  `ι_{1,1}`) and the Künneth isomorphism (3.39) (`EQK0.kunneth`), the symbols of `Ind_{m,n}` and `Res_{m,n}` give the
  structure constants of `u⁺`: `1·1 = 1`, `1·E = E·1 = E`, `E·E = 0`, `r(1) = 1 ⊗ 1`, `r(E) = E ⊗ 1 + 1 ⊗ E`
  (`thm_3_18_mul_one_one`, `thm_3_18_mul_one_E`, `thm_3_18_mul_E_one`, `thm_3_18_mul_E_E`, `thm_3_18_comul_one`,
  `thm_3_18_comul_E_left`, `thm_3_18_comul_E_right`); all other components have source or target `0`. `Res_{m,n}`
  for `m + n ≤ 1` is computed as derived induction along `ι_{m,n}^{-1}`. **Thm 3.18 over `ℤ`**
  (`Frontier.EQThm318Int`, the integral dg rings themselves): the unit `ℤ → OPol_N` is a quasi-isomorphism for
  `N ≤ 1` (`EQK0.intUnit_opol_isQuasiIso`, from `H(OPol_N) = ℤ · 1`, `Frontier.EQSmallRankDG`), so
  `K₀(D(OPol_N)^c) ≅ K₀(D(ℤ)^c) ≅ ℤ` (dg-lean's quasi-isomorphism invariance of `K₀` and `K₀(ℤ) ≅ ℤ`;
  `EQK0.baseK0OPolInt`) and `K₀(D(ONH_N)) ≅ ℤ[√−1]` (`superK0OPolIntEquiv`); `K₀(D(ONH_n)) = 0` for `n ≥ 2`
  (`superK0c_onh_int_eq_zero`); with the Künneth isomorphism (3.39) for `m + n ≤ 1` (`kunnethInt`) the same
  structure constants hold (`thm_3_18_int_*`). For `E · E` the Künneth map `[ONH_1] ⊗ [ONH_1] ↦ [ONH_1 ⊗ ONH_1]`
  (`kunnethMapInt`) suffices, since the product lands in `K₀(D(ONH_2)) = 0`; it is in fact the Künneth
  isomorphism over `ℤ` (`Frontier.EQKunnethInt`: `OPol_1 ⊗ OPol_1` has `Z¹ = 0` and torsion-free `H²`, so
  `K₀(D(OPol_1 ⊗ OPol_1)^c) ≅ ℤ`; `EQK0Int.kunnethOneOneInt`, `kunnethMapInt_one_one_eq`), so (3.39) holds over `ℤ`
  for all `m, n ≤ 1`.
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
  This does not assert tensor-product multiplicativity, the case over `ℤ`, or the later
  nilHecke categorification theorems.
- The diagonal half-grading on the existing integral odd nilHecke dg ring (`Frontier.EQDiagonal`):
  `EQDiagonal.onh n` places `ONH_{n+2}`'s ordinary degree `k` at `(2k, k mod 2)`; its actual dots
  and crossings have bidegrees `(2,1)` and `(-2,1)`. The original differential is unchanged,
  including `d(xᵢ) = xᵢ²`, `d(∂ᵢ) = 1`, and bidegree `(2,1)`. This is a ring-level bridge,
  not by itself a derived module comparison or compact-generator result.
- For the entire half-graded module category of integral `ONH_{n+2}` (`Frontier.EQHalfGradedAcyclic`),
  the crossing contracts every weight, with no parity-versus-degree support restriction:
  `isAcyclic_halfGraded`, `isZero_halfGraded_derivedCategory`. Both ordinary and super Grothendieck
  groups of compact objects vanish (`compactK0_eq_zero`, `superK0c_eq_zero`). These statements cover
  ranks at least two only; the integral half-graded compact Grothendieck-group calculation in
  ranks zero and one and tensor multiplicativity remain open.
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
  sends each weight representable to the representable at that same weight. Numerical
  compact `K₀` and tensor multiplicativity remain open; the super-`K₀` comparison is below.
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
  is used. Numerical calculations and tensor multiplicativity remain open.
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
  universe is independent. Numerical calculations and tensor multiplicativity
  remain open; no all-rank induction equivalence is asserted.
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

## Building

Requires [elan](https://github.com/leanprover/elan). Toolchain `leanprover/lean4:v4.34.1` and Mathlib
`v4.34.1` (`d13f23b723b8a846827a245b89c10fc7d3f11612`) are pinned. The diagrammatic modules depend on
string-diagrams-lean at `fb96f497c0dd0a24ed941d3a2c25b4cbfe63d884`, and the [EQ] dg structures on
[dg-lean](https://github.com/apellis/dg-lean) at `6cf0ba0d4f19bdceed05f3caf8b83e5b0929d243` (see
`lakefile.lean` and `lake-manifest.json`).

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
