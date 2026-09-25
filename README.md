# odd-lean

A Lean 4 / Mathlib formalization of results on odd symmetric functions and the odd
nilHecke algebra, together with machine-checked errata to the source papers.

Sources (numbering below refers to these arXiv versions):

- **[EK]** A. P. Ellis, M. Khovanov, *The Hopf algebra of odd symmetric functions*,
  arXiv:1107.5610v2.
- **[EKL]** A. P. Ellis, M. Khovanov, A. D. Lauda, *The odd nilHecke algebra and its
  diagrammatics*, arXiv:1111.1320v1.
- **[E]** A. P. Ellis, *The odd Littlewood–Richardson rule*, arXiv:1111.3932v1.

The library builds with no `sorry` and no added axioms. The printed axiom closures of
the results listed below contain only `propext`, `Classical.choice` and `Quot.sound`.
The [EK] results are formalized at q = −1 over ℤ (§2.1 also at general q). Signs are
taken exactly as printed; every corrected statement is a separate declaration.

## Formalized results

All names are in `OddMath.Frontier`; module `M` is `OddMath/Frontier/M.lean`.

### [EK]

| Result | Declaration |
|---|---|
| Thm 3.7, (3.9), all degrees | `EKClosureComposition.identity39` |
| (3.8), entrywise sign (corrected labels, erratum 10) | `EKRskSign.thm_3_7_sign` |
| Cor 3.8, (3.10) | `EKClosureComposition.corollary_3_8` |
| Cor 3.9, (3.11) | `EKClosureComposition.corollary_3_9` |
| Prop 3.10 | `EKClosureComposition.proposition_3_10` |
| Lemma 3.11, (3.13) | `EKFinalClosure.lemma_3_11` |
| Cor 3.12, (3.14) | `EKFinalClosure.cor_3_12_first`, `EKFinalClosure.cor_3_12_second` |
| Cor 3.13, (3.15) | `EKFinalClosure.cor_3_13` |
| Prop 3.3 | `EKPrimitives.proposition_3_3` |
| Prop 3.4 | `EKCenterPower.center_iff` |
| (3.3) | `EKDualBases.h_eq_M_f` |
| (3.4), corrected (erratum 6) | `EKDeterminantCorrected.det_M`, `EKDeterminantCorrected.printed_iff` |
| §2.1 at general q; Prop 2.2, (2.3) | `EKGeneralQ.ek_sec21_general_q`, `EKGeneralQ.adjointness` |
| Prop 2.6 | `EKMixedPairing.proposition_2_6` |
| Prop 2.11, (2.16)–(2.17) | `EKQuotientRelations.mixed_even`, `EKQuotientRelations.mixed_odd` |
| Prop 2.14, (2.20)–(2.21) | `EKSemiorthogonality.proposition_2_14_diagonal`, `EKSemiorthogonality.proposition_2_14_vanishing` |
| Lemma 2.16 | `EKTriangular.psi3_triangular_remainder` |
| (2.24), corrected (erratum 3) | `EKAutomorphisms.psi3_hWord_source` |
| (2.25) | `EKAntipode.S_hWord` |
| Thm 4.1 | `EKClassicalPlactic.theorem_4_1` |
| Thm 4.3, corrected contents (erratum 10) | `EKRskBijection.rsk_bijective` |
| (4.4) | `EKRskBijection.ek_eq_4_4` |
| Appendix §§5.1–5.2, degrees ≤ 5 | module `EKAppendixData` |

Not fully formalized: Lemma 2.15 (the e-side restricted nondegeneracy is proved for
every λ as `EKProp310.eAbove_restricted_nondeg`; the h-side is not). No result above
depends on it.

### [E]

| Result | Declaration |
|---|---|
| Thm 3.8: s^K_λ = s^p_λ = s^s_λ, for N ≥ 2 variables and λ with at most N rows | `OddLRThm38.thm38` |
| Companion statement for λ with more than N rows | `OddLRThm38.thm38_tall` |
| (3.10), vertical Pieri rule | `OddLRVerticalPieri.vertical_pieri` |
| π_N s^K_λ = s^p_λ (identification with [EK]) | `OddLREKIdentification.piN_schurK` |

Cor 3.9 and Section 4 of [E] (including the odd Littlewood–Richardson rule) are not
formalized.

### [EKL], Section 2 (selection)

| Result | Declaration |
|---|---|
| (2.4) | `TwistedLeibniz.div1_mul` |
| Prop 2.1, (2.9) | `DividedDistant.divided_distant` |
| Prop 2.2 | `ElementaryGeneration.kernel_eq_elementaryClosure` |
| Lemma 2.10 | `LongestDivided.D_staircase` |
| Prop 2.11 | `NilCoxeterPresentation.action_injective`, `OddSchubertAction.left_relation_coefficients` |
| (2.42), corrected selector (erratum 12) | `OddSchubertAction.action_additive` |
| Prop 2.13 | `SchubertBasis.left_kernel_decomposition_unique`, `SchubertBasis.right_kernel_decomposition_unique` |
| Prop 2.15, corrected (erratum 14) | `CenterCorrected.center_oddSymmetric`, `CenterCorrected.center_nilHecke` |
| Lemma 2.18, for the printed block word | `OmissionCanonical.trichotomy` |
| Lemma 2.18, corrected (erratum 15) | `OwlGeneral.owl_general`, `OwlGeneral.left_kernel_owl_class` |
| Lemma 2.19(2), (2.61) | `NonadjacentDivided.anticommutation` |
| (2.64) | `OddSymmetrizer.D_left_kernel` |
| Cor 2.22 | `OddSymmetrizer.S_eq_self`, `OddSymmetrizer.S_idempotent` |
| Cor 2.23, (2.66) | `LongestReversal.action_D` |
| Prop 2.26, (2.71) | `OddSchurPieri.right_pieri` |
| Prop 2.2 in q-series form (2.18), (2.20); (2.52); (2.67) | `EKLSectionTwo.qrk_symmetric`, `EKLSectionTwo.symRank_mul_qPoch`, `EKLSectionTwo.qfactorial_eq`, `EKLSectionTwo.box_qcard` |
| (2.19), corrected (erratum 23) | `EKLSectionTwo.qrkPol_eq` |
| (2.13), (2.27): reduction mod 2 | `EKLSectionTwo.polynomialModTwo`, `EKLSectionTwo.symmetricModTwo` |
| (2.25) | `EKLSectionTwo.reorder_even`, `EKLSectionTwo.reorder_odd` |
| (2.33) | `EKLSectionTwo.mixed_even`, `EKLSectionTwo.mixed_odd` |
| (2.34), corrected index | `EKLSectionTwo.complete_last` |
| (2.6), (2.11), (2.45); Remark 2.17; (2.59) | `EKLSectionTwo.divided_even_power_sum`, `EKLSectionTwo.psi_homotopy`, `EKLSectionTwo.schubert_identity_action`, `EKLSectionTwo.s_elementary_one_not_mem`, `EKLSectionTwo.dividedPair_elementary_one` |
| (2.72), Remark 2.27 (horizontal Pieri) | `EKLSectionTwo.horizontal_pieri`, `EKLSectionTwo.horizontal_pieri_Q` |
| (2.73)–(2.74), with η_α made precise (erratum 27) | `EKLSectionTwo.reverse_sK`, `EKLSectionTwo.left_vertical_pieri`, `EKLSectionTwo.left_horizontal_pieri` (and `…_Q` in OΛ) |
| (2.49)–(2.51), corrected (erratum 28); (2.63); (2.53) for OPol_a over OΛ_a; Cor 2.6 at a = 2 | `EKLSectionTwo.eq_2_49_sum_from_zero`, `EKLSectionTwo.eq_2_50_first`, `EKLSectionTwo.eq_2_50_sum_from_zero`, `EKLSectionTwo.eq_2_51`, `EKLSectionTwo.eq_2_63`, `EKLSectionTwo.eq_2_53`, `EKLSectionTwo.cor_2_6_rank_two` |
| Remark 2.28: (2.76) corrected (erratum 22); ε_4 not generated; no naive Jacobi–Trudi | `EKLSectionTwo.schur_two_two`, `EKLSectionTwo.complete_two_two`, `EKLSectionTwo.complete_three_one`, `EKLSectionTwo.elementary_four_not_mem`, `EKLSectionTwo.schur_ne_elementary_determinant`, `EKLSectionTwo.schur_ne_complete_determinant` |

### [EKL], §§3–4 (rank a = n+2 ≥ 2 unless noted)

| Result | Declaration |
|---|---|
| (3.17)–(3.18), 0-Hecke relations | `ZeroHecke.zeroHecke_sq`, `ZeroHecke.zeroHecke_braid`, `ZeroHecke.zeroHecke_distant` |
| e_a = ∂̄_{w0} is independent of the reduced word | `ZeroHecke.projector_eq_of_reduced` |
| Prop 3.5 | `ZeroHecke.prop_3_5` |
| Prop 3.6 | `ZeroHecke.DElem_mul_zeroHecke`, `ZeroHecke.DElem_mul_projector`, `ZeroHecke.projector_mul_projector` |
| Prop 3.7 | `StrandCrossing.prop_3_7` |
| (3.42) | `StrandCrossing.crossing_3_42` |
| Lemmas 3.1–3.3 (on any window) | `ThickRelations.lemma_3_1`, `ThickRelations.lemma_3_2`, `ThickRelations.lemma_3_3` |
| (3.28), (3.29), (3.31); Remark 3.4 ((3.30) fails) | `ThickRelations.eq_3_28`, `ThickRelations.eq_3_29`, `ThickRelations.eq_3_31`, `ThickRelations.remark_3_4` |
| (3.40), (3.43), (3.44) | `ThickRelations.eq_3_40`, `ThickRelations.eq_3_43`, `ThickRelations.eq_3_44` |
| §3.3, σ; (3.46)–(3.50), (3.52)–(3.54) | `OnhReflection.sigma`, `OnhReflection.eq_3_50`, `OnhReflection.eq_3_52`, `OnhReflection.eq_3_53`, `OnhReflection.eq_3_54` |
| (3.51), corrected (erratum 18) | `OnhReflection.eq_3_51` |
| Def 4.3, (4.8)–(4.11) | `ThickDots.projector_poly_projector`, `ThickDots.projector_poly_projector_eq`, `ThickDots.thick_mul` |
| (4.19), (4.20) | `ThickDots.schur_eq`, `ThickDots.skewSign_delta` |
| (4.21)–(4.22); Def 4.10 and the identity after it | `ThickDots.projector_schur_projector`, `ThickDots.projector_dualSchur_projector` |
| (4.1), (4.51), (4.53): splitters, σ_α, λ_α | `ThickBubble.splitter`, `ThickBubble.sigma`, `ThickBubble.lam` |
| (4.2) thick crossing; Prop 4.1 (4.3)–(4.4); Prop 4.2 (4.5)–(4.6) | `ThickRelations.eq_4_2`, `ThickRelations.prop_4_1_split`, `ThickRelations.prop_4_1_merge`, `ThickRelations.prop_4_2_left`, `ThickRelations.prop_4_2_right` |
| Explosions (4.13)–(4.16); (4.42); (4.46); Remark 4.12 | `ThickRelations.eq_4_13`, `ThickRelations.eq_4_14`, `ThickRelations.eq_4_15`, `ThickRelations.eq_4_16`, `ThickRelations.eq_4_42`, `ThickRelations.eq_4_46`, `ThickRelations.remark_4_12` |
| Prop 4.11 (all a, b ≥ 0) | `ThickBubble.prop_4_11` |
| (4.54), (4.55) | `ThickBubble.eq_4_54`, `ThickBubble.eq_4_55` |
| (4.41) | `ThickMatrixUnits.eq_4_41` |
| Lemma 4.13 | `ThickMatrixUnits.lemma_4_13` |
| Lemma 4.14 | `ThickMatrixUnits.lemma_4_14` |
| Thm 4.15 | `ThickMatrixUnits.thm_4_15_orthogonal`, `ThickMatrixUnits.thm_4_15_sum` |
| Thm 4.16, (4.56)–(4.57) (all a, b ≥ 0) | `ThickDecomposition.thm_4_16`, `ThickDecomposition.eq_4_57` |

### [EKL], §5 (rank a = n+2 ≥ 2)

| Result | Declaration |
|---|---|
| OH_{a,N}, ONH_a^N (p. 44); OH_{a,N} = 0 for N < a; OH_{a,a} ≅ ℤ | `Cyclotomic.OH`, `Cyclotomic.ONH`, `Cyclotomic.OH_subsingleton`, `Cyclotomic.OH_self_equiv` |
| (5.3) and the inverse limit (p. 44) | `OddSymmetricLimit.equation_5_3`, `OddSymmetricLimit.transition`, `OddSymmetricLimit.inverse_limit` |
| (5.5)–(5.7) | `Cyclotomic.supercentral_inverse`, `Cyclotomic.supercentral_inverse_unique`, `Cyclotomic.span_grassmannRelations` |
| Lemma 5.1, corrected (erratum 19) | `Cyclotomic.lemma_5_1`, `Cyclotomic.lemma_5_1_left` |
| Prop 5.2 (ungraded) | `Cyclotomic.prop_5_2` |
| Conj 5.3 (a theorem for a ≥ 2) | `OddGrassmannSchur.conjecture_5_3` |
| Prop 5.4 | `OddGrassmannSchur.proposition_5_4`, `OddGrassmannSchur.toOHQ_sK_eq_zero`, `OddGrassmannSchur.finrank_OH` |

### [EKL], §6 (rank a = n+2 ≥ 2)

| Result | Declaration |
|---|---|
| (6.1): ONH_a ≅ ⊕_{ℓ∈Sq(a)} ONH_a e_a as left modules, with degrees | `Categorification.eq_6_1`, `Categorification.eq_6_1_hasDegree` |
| (6.2): ONH_{a+b}(e_a ⊗ e_b) ≅ ⊕_{α∈P(a,b)} ONH_{a+b} e_{a+b}, with degrees | `Categorification.eq_6_2`, `Categorification.eq_6_2_hasDegree` |
| ONH_a^N = 0 for N < a (p. 47) | `Categorification.cyclotomic_vanish` |
| K_0(ONH_a) ≅ ℤ[q,q⁻¹], free on [E^{(a)}], E^{(a)} = ONH_a e_a with its shift (every a ≥ 0) | `OddCategorification.basisE`, `OddCategorification.rankEquiv_Eclass` |
| (6.1) in K_0, shifts corrected (erratum 26): [ONH_a] = [a]! [E^{(a)}] | `OddCategorification.eq_6_1_K0`, `OddCategorification.eq_6_1_qFact` |
| (6.2) in K_0: [E^{(a)}E^{(b)}] = [a+b, a] [E^{(a+b)}] | `OddCategorification.eq_6_2_K0`, `OddCategorification.indClass_eq` |
| (6.3): U_q^+(sl_2)_A ≅ K_0(ONH) as ℤ[q,q⁻¹]-algebras, ϑ^{(a)} ↦ [E^{(a)}] | `OddCategorification.eq_6_3`, `OddCategorification.eq_6_3_UA` |

Here K_0 is the Grothendieck group of finitely generated graded projective modules, presented by
graded idempotent matrices up to Murray–von Neumann equivalence (`GradedK0`); every such module is
a sum of shifts of E^{(a)} with determined multiplicities (classification over the connected
graded ring OΛ_a and graded Morita invariance, which replace the paper's appeal to graded
locality). The product on K_0(ONH) is induction realized on the indecomposables: E^{(a)} ⊠ E^{(b)}
induces to ONH_{a+b}(e_a ⊗ e_b); induction is not constructed as a functor on all graded
projective modules. U_q^+(sl_2)_A is Lusztig's integral form (`QuantumSl2Plus.UA`).

### [EKL], §4.3.1 (every rank)

| Result | Declaration |
|---|---|
| Lemma 4.4 (Shuffle Lemma) | `ShuffleLemma.shuffle_one`, `ShuffleLemma.shuffle_even`, `ShuffleLemma.shuffle_odd` |
| (4.27), corrected (erratum 17) | `ShuffleLemma.big_shuffle` |
| Prop 4.5, in `m` variables | `StaircaseEvaluation.prop_4_5` |
| Prop 4.6 | `StaircaseEvaluation.prop_4_6` |
| Prop 4.7 | `MonomialReversal.prop_4_7` |
| Lemma 4.8 | `StaircaseEvaluation.lemma_4_8` |
| Lemma 4.9, with Ω as in (4.34) | `StaircaseEvaluation.lemma_4_9` |

Lemmas 4.8–4.9 are proved by a different route from the printed one: if every exponent is at
most `N−1` and the degree is not `binom(N,2)`, then `D_N(x^γ) = 0`
(`StaircaseSorting.D_monomial_eq_zero_of_bounded`); and for a monomial whose exponents strictly
decrease and then strictly increase, `D_N(x^γ)` in degree `binom(N,2)` is `0` unless the
exponents are distinct, and then `(−1)^{binom(N,3) + Σ binom(v,3)}`, the sum over the exponents
of the increasing part (`StaircaseValley.top_valley`).

Files named `*Controls.lean`, `*Audit.lean` and `OddMath/Tests/*` contain finite
checks and axiom printouts, not results.

## Errata

Codes: **M** misprint; **F→T** false as printed, true corrected statement given;
**G** gap in the proof of a true statement; **X** false as printed, no correction
given here. A declaration name means the item is Lean-checked; otherwise it is marked
*not formalized*.

### [EK] arXiv:1107.5610v2

1. **Prop 2.11 proof, p. 15, even-case recurrence [M].** Uses `e_k` where the other
   generator is needed; correct recurrence `EKQuotientRelations.pairing_he_strip`.
   (2.16)–(2.17) are unaffected. Numerical counterexample *not formalized*.
2. **Example ℓ(w_(4,4,2,1)), p. 16 [M].** 23 inversions (sign −1), not 22.
   *Not formalized.*
3. **(2.24) [M].** Exponent `λ_j λ_j` should be `Σ_{i<j} λ_i λ_j`;
   `EKAutomorphisms.psi3_hWord_source`.
4. **Step before (2.26), p. 21 [G].** One transformation is omitted when ψ₃ is applied
   to (2.5); (2.26) is unaffected. *Not formalized.*
5. **Lemma 2.15 proof, p. 18 [G].** The equality `(H_{≥λ})^⊥ = E_{>λᵀ}` (lexicographic
   order) used in the proof is false at λ = (3,3):
   `EKRestrictedPairing.complement_equality_false`. The e-side conclusion is proved
   independently (`EKProp310.eAbove_restricted_nondeg`); the h-side is not formalized.
6. **(3.4), p. 23 [F→T].** False as printed: `det M₂ = −1`
   (`EKDeterminant.equation_3_4_counterexample`), independent of ordering
   (`EKDeterminant.counterexample_under_every_order`). Correct formula, all d:
   `det M_d = (−1)^{(p(d)−sc(d))/2} · Π_{λ=λᵀ} (−1)^{ℓ(w_λ)}`, where sc(d) counts
   self-conjugate partitions (`EKDeterminantCorrected.det_M`). The printed formula
   holds exactly when `(p(d)−sc(d))/2` is even (`EKDeterminantCorrected.printed_iff`).
7. **Uniqueness of Schur functions via Lemma 2.15, p. 29 [G].** The cited argument
   fails (item 5); uniqueness holds: `EKSchurOrthonormal.schur_val_unique`.
8. **Prop 3.10 proof, p. 29 [G].** The intersection claimed one-dimensional has
   dimension ≥ 2 at λ = (3,3) (*not formalized*). Prop 3.10 holds:
   `EKClosureComposition.proposition_3_10`.
9. **Lemma 3.11 proof, pp. 29–30 [G, M].** Same one-dimensionality failure at
   λ = (2,2,2); swapped indices; `h_μ` for `e_μ`. The lemma holds:
   `EKFinalClosure.lemma_3_11`. Misprint readings *not formalized*.
10. **(4.3) and Example 4.5 [F→T].** The printed codomain (cont P = μ, cont Q = ρ) is
    impossible when μ ≠ ρ (`EKRskBijection.printed_codomain_obstruction`,
    `EKRskBijection.ex45_printed_obstruction`). With the contents swapped, Thm 4.3
    holds (`EKRskBijection.rsk_bijective`). (4.4) holds as printed.
11. **(3.8) [M].** Same label swap as item 10; the sign identity holds
    (`EKRskSign.thm_3_7_sign`).

### [EKL] arXiv:1111.1320v1

12. **(2.43) [F→T].** Selector w = u⁻¹ should be w = u
    (`OddSchubertAction.action_additive`).
13. **At (2.65) [M].** Extra staircase factor in the leftmost argument; correct:
    `OddSymmetrizer.S_eq_self`.
14. **Prop 2.15, centre of OΛ_N and ONH_N [F→T].** The printed description (symmetric
    polynomials in x₁², …, x_N²) is correct exactly for even N
    (`CenterCorrected.printed_iff_even`, `CenterCorrected.printed_iff_even_nilHecke`); for
    N = 3, x₁x₂x₃ is central but not of that form
    (`NilHeckeCenter.kernel_center_counterexample`). The first step of the proof ("doing this
    for each j separately") fails: xᵃ commutes with every xⱼ iff |a| − aⱼ is even for all j,
    which for odd N also allows all exponents odd (`CenterPoly.mem_center_iff`). Correct
    statement, every N ≥ 2: the centre of OΛ_N is {a + x₁⋯x_N·b : a, b symmetric in
    x₁², …, x_N²}, with b = 0 for even N, and the centre of ONH_N is its image under the dot
    inclusion (`CenterCorrected.center_oddSymmetric`, `CenterCorrected.center_nilHecke`).
15. **Lemma 2.18 (OWL) for an arbitrary reduced word of w₀ [F→T].** Counterexample in
    5 variables, word `[0,1,0,3,2,1,0,3,2,1]`: `OwlDirect.owl_trichotomy_false`. The
    proof reorders the D_a termwise; distant commutations preserve OWL, but a single
    braid move need not (`OwlBraid.braid_transport_false`). Corrected statement, every
    N ≥ 2 (letters 0, …, N−2): OWL, and the kernel identity (2.64), hold for every word in
    `OwlGeneral.OwlClass` (`OwlGeneral.owl_general`, `OwlGeneral.left_kernel_owl_class`).
    This class is built from the empty word by (i) prepending the chain
    (N−2, N−3, …, N−2−r) to a class word on the top r+1 strands, and (ii) the flip
    i ↦ 2N−3−r−i of the top r+1 strands, and is closed under distant commutations. Its
    words are reduced words of w₀ (`OwlGeneral.owlClass_reduced_longest`); it contains
    the printed block word, which is the case used for (2.64)
    (`OwlGeneral.blockClass_owlClass`, `OmissionCanonical.trichotomy`), and is strictly
    larger (`OwlGeneral.not_blockClass_stageExample`). Whether OWL holds for words
    outside this class is open. (2.64), Cor 2.22 and Cor 2.23 are proved.

### [E] arXiv:1111.3932v1

16. **Lemma 3.5 [F→T].** The lexicographic order must be taken on λᵀ; with row-lex the
    statement fails (`OddLREliminationControls.row_lex_variant_fails`). Thm 3.8 holds.

### [EKL] arXiv:1111.1320v1, §2 (continued)

22. **Remark 2.28, (2.76) and the h-expansions [F→T].** s₂₂ = −ε₂₂ + ε₃₁ + 2ε₄ for a ≥ 4
    (`EKLSectionTwo.schur_two_two`), not ε₂₂ + ε₃₁ − 2ε₄, nor its negative
    (`EKLSectionTwo.printed_schur_two_two_false`, `…_false_neg`); h₂₂ = ε₂₂ + 2ε₂₁₁ + ε₁₁₁₁ and
    h₃₁ = ε₃₁ + ε₁₁₁₁ (`EKLSectionTwo.complete_two_two`, `EKLSectionTwo.complete_three_one`;
    printed forms refuted: `EKLSectionTwo.printed_complete_determinant_false`). The conclusions of
    the Remark hold (`EKLSectionTwo.schur_ne_elementary_determinant`,
    `EKLSectionTwo.schur_ne_complete_determinant`, `EKLSectionTwo.elementary_four_not_mem`).
23. **(2.19) [M].** The exponent is q^{2ℓ(σ)}, not q^{ℓ(σ)}: `EKLSectionTwo.qrkPol_eq`; printed form
    refuted by `EKLSectionTwo.printed_qrk_quotient_false`.
24. **Proof of Prop 2.2, p. 8 [M].** The leading term of ε_α is x^{αᵀ} with coefficient ±1, not x^α
    with coefficient 1 (`EKLSectionTwo.printed_leading_term_false`).
25. **(2.34) [M].** The index k is unbound; with h_{m−j} the formula holds
    (`EKLSectionTwo.complete_last`).

27. **Remark 2.27, (2.73)–(2.74) [G].** η_α is not defined in [EK], and ψ₃ does not act diagonally
    on Schur functions (`EKLSectionTwo.psi3_not_diagonal`). With η_λ defined by R(s_λ) = η_λ s_λ for
    the anti-involution R fixing every h_n (`EKLSectionTwo.reverse_sK`), both identities hold as
    printed, in OΛ and in every OΛ_a (`EKLSectionTwo.left_vertical_pieri`,
    `EKLSectionTwo.left_horizontal_pieri`).
28. **(2.49)–(2.51) [M, G].** In (2.49) and in the second equality of (2.50) the sums must start at
    k = 0 (f = 1 is a counterexample: `EKLSectionTwo.eq_2_49_printed_fails`,
    `EKLSectionTwo.eq_2_50_printed_fails`; corrected: `EKLSectionTwo.eq_2_49_sum_from_zero`,
    `EKLSectionTwo.eq_2_50_sum_from_zero`). The step "h·x_{a−1}^i ∈ H_{a−1}" in the proof of (2.51)
    is false for H of (2.46); (2.51) holds (`EKLSectionTwo.eq_2_51`).
29. **(2.63) [M].** In the case ℓ = j − i the word should read s_{i+1}⋯s_{j−1}s_{i,j}; the identity
    holds for all g, h ∈ OΛ_a (`EKLSectionTwo.eq_2_63`).

### [EKL] arXiv:1111.1320v1, §4

17. **(4.27), "big odd shuffle" [F→T].** The printed coefficient `(−1)^{m(j+1)}` is wrong
    from `j = 3` on; the formula fails for `m = 0, k = 7` (`ShuffleLemma.big_shuffle_false`).
    Correct coefficient: `(−1)^{binom(j,2) + (m+1)(j+1)}`, all `m` and odd `k`
    (`ShuffleLemma.big_shuffle`). Lemma 4.4, Props 4.5–4.7 and Lemmas 4.8–4.9 hold as printed.

18. **(3.51) [F→T].** `D_a = σ(D_a)` holds, but `ψ(D_a) = (−1)^{binom(a,4)} D_a` (and likewise
    for `ψσ(D_a)`), not `(−1)^{binom(a−1,4)}`; the printed sign fails at `a = 4`
    (`OnhReflection.eq_3_51_false`, `OnhReflection.eq_3_51_printed_false`). Corrected:
    `OnhReflection.eq_3_51`. (3.52)–(3.54) hold as printed.

### [EKL] arXiv:1111.1320v1, §5

19. **Lemma 5.1, (5.4) [F→T].** For the action of Corollary 2.14 (on OPol_a as a right
    OΛ_a-module) the printed matrix is not the matrix of φ(x̃_1) on B_β: at a = 2, β = 0 it gives
    x_1² = x_1ε_1 + ε_2, whereas x_1² = x_1ε_1 − ε_2 (`Cyclotomic.lemma_5_1_printed_false`). The
    first column is (−1)^{j(|β|+1)+1} ε_j (`Cyclotomic.lemma_5_1`). The display in the proof holds
    with left coefficients (`Cyclotomic.lemma_5_1_left`).
20. **Proof of Prop 5.2, (5.8)–(5.9) [M].** In (5.8) the exponent C(N−a,2) should be C(N−a+2,2)
    (`Cyclotomic.eq_5_8_false`, `Cyclotomic.choose_two_parity`); in the second case of (5.9) the
    sign is −(−1)^{a(N−a+1)} (`Cyclotomic.eq_5_9_false`, `Cyclotomic.eq_5_9_top`). Prop 5.2 holds
    (`Cyclotomic.prop_5_2`, proved by a different route); in right coordinates the ideal
    generated by the entries of x̃_1^N is the image of ⟨h_m : m > N−a⟩ under the w_0-reversal
    (`Cyclotomic.entryIdeal_eq_rev`).
21. **Proof of Prop 5.4 [G].** It uses that OH_{a,N} is a free ℤ-module without proof. Prop 5.4
    holds, and OH_{a,N} is free of rank C(N,a) (`OddGrassmannSchur.proposition_5_4`,
    `OddGrassmannSchur.finrank_OH`).

### [EKL] arXiv:1111.1320v1, §6

26. **(6.1) [M].** The grading shifts of the summands are C(a,2) − 2|ℓ| (the exponents of [a]!),
    not a − 1 − 2|ℓ|; the printed shifts fail at a = 3 for either sign convention
    (`OddCategorification.eq_6_1_printed_false`). Corrected: `OddCategorification.eq_6_1_K0`.

These errata arose during the formalization; they are not a complete review of the
papers.

## Building

Requires [elan](https://github.com/leanprover/elan). Toolchain
`leanprover/lean4:v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` are
pinned.

```sh
lake exe cache get
lake build
```

## Models used

The code and proofs were produced with AI models under human direction and checked
by Lean:

- GPT-6 Astra
- Muse Spark 1.3
- Claude Opus 5.5

## License

Released under the Apache License 2.0; see [`LICENSE`](LICENSE).
