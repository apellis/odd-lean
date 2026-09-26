# Errata

Errata to the source papers found during the formalization, one list per paper, in order of
appearance. Numbering refers to the arXiv versions cited in [README.md](README.md). All names are
in `OddMath.Frontier`.

Codes: **M** misprint; **F→T** false as printed, with a corrected statement proved; **G** gap in
the proof of a true statement. Every item carries the Lean declarations that refute the printed
claim and prove the correction, except where it is marked *textual*: such an item is a slip in
the prose with no mathematical content to check.

These errata are what the formalization turned up; they are not a complete review of the papers.

## [EK] A. P. Ellis, M. Khovanov, *The Hopf algebra of odd symmetric functions*, arXiv:1107.5610v2

1. **Prop 2.3 and Cor 2.4, over an arbitrary ground ring [F→T].** The paper works over any
   commutative ring k and any q ∈ k (p. 5). Over k = ℤ/4 with q = 2, the radical I is not a
   coideal: an element x ∈ I in degree 4 has Δ(x) ∉ I⊗Λ′ + Λ′⊗I, and no coproduct on Λ = Λ′/I is
   compatible with Δ (`EKGeneralQ.coideal_counterexample`, `EKGeneralQ.no_quotient_coproduct`).
   The ideal half of Prop 2.3 holds for every k and q (`EKGeneralQ.prop_2_3_ideal`). Δ(I) always
   lies in the radical of the tensor form (`EKGeneralQ.coproduct_radical_annihilates`), and the
   coideal property and Cor 2.4 hold whenever pure tensors separate points of Λ⊗Λ
   (`EKGeneralQ.prop_2_3_coideal_of_separating`, `EKGeneralQ.cor_2_4_of_separating`). That covers
   every principal ideal domain and every q (`EKGeneralQ.separating_of_pid`), and every k at
   q = ±1 (`EKGeneralQ.prop_2_3_coideal_neg_one`, `EKGeneralQ.prop_2_3_coideal_one`).
2. **Prop 2.11 proof, p. 15, even-case recurrence [M].** It uses `e_k` where the other generator
   is needed. The correct recurrence is `EKQuotientRelations.pairing_he_strip`; (2.16)–(2.17) are
   unaffected. At a = b = k = 2 the printed recurrence gives −1 for (h₂e₂, e₂h₂) = −2
   (`ErrataChecks.prop_2_11_printed_even_instance`, `ErrataChecks.prop_2_11_printed_even_false`).
3. **Example ℓ(w_(4,4,2,1)), p. 16 [M].** 23 inversions (sign −1), not 22 (`ErrataChecks.ell_4421`, `ErrataChecks.pairing_4421`).
4. **p. 16, refining dominance so that reversal swaps transposes [F→T].** For n ≥ 8 there are two
   distinct self-conjugate partitions, and both would have to occupy the middle position, so no
   total order on the partitions of n (refining dominance or not) has this property
   (`EKMore.no_rev_swaps_ge_eight`, `EKMore.two_self_transpose`). Such a refinement exists exactly
   for n ≤ 7 (`EKMore.ek_p16_refinement_iff`). The remaining claims of the paragraph hold
   (`EKMore.ek_p16_total_iff`, `EKMore.ek_p16_graded_iff`, `EKMore.ek_p16_lowest_incomparable`,
   `EKMore.ek_p16_lex_reversal_iff`).
5. **Lemma 2.15 proof, p. 18 [G].** The equality `(H_{≥λ})^⊥ = E_{>λᵀ}` (lexicographic order)
   used in the proof is false at λ = (3,3) (`EKRestrictedPairing.complement_equality_false`).
   Lemma 2.15 holds; both Gram determinants are ±1 (`EKComplete.lemma_2_15`,
   `EKComplete.lemma_2_15_det`).
6. **p. 18, "ψ₃ … (not a coalgebra homomorphism)" [F→T].** ψ₃ satisfies Δψ₃ = (ψ₃ ⊗ ψ₃)Δ and
   εψ₃ = ε (`EKMore.ek_p18_psi3_coalgebra_hom`, `EKMore.ek_p18_psi3_printed_false`). The statement
   for ψ₂ holds (`EKMore.ek_p18_psi2_not_coalgebra`).
7. **§1 and §2.3 over a ground ring with 2 = 0 [F→T].** From §2.2 on q = −1, which equals 1 when
   2 = 0 in k; then Λ_k is the classical commutative algebra, and several assertions fail (over
   𝔽₂: `EKOverK.F2_commutative`, `EKOverK.F2_psi1K_involutive`, `EKOverK.F2_orderOf_psi1K`,
   `EKOverK.F2_card_closure`, `EKOverK.F2_SK_involutive`, `EKOverK.F2_psi3K_e`). Exact hypotheses:
   Λ_k is commutative, equivalently cocommutative, equivalently ψ₂ = id, ψ₁ is an involution, or
   S² = 1, iff 2 = 0 in k (`EKOverK.commutative_iff`, `EKOverK.cocommutative_iff`,
   `EKOverK.psi2K_eq_one_iff`, `EKOverK.psi1K_involutive_iff`, `EKOverK.SK_involutive_iff`);
   ψ₃(e_n) = e_n iff n ≤ 1 or 2 = 0 (`EKOverK.psi3K_e_iff`); ψ₁ has finite order iff 2 is
   nilpotent in k, and ⟨ψ₁, ψ₂⟩ ≅ ℤ/2 ∗ ℤ/2 iff 2 is not nilpotent
   (`EKOverK.isOfFinOrder_psi1K_iff`, `EKOverK.rhoK_injective_iff`).
8. **(2.24) [M].** The exponent `λ_j λ_j` should be `Σ_{i<j} λ_i λ_j`
   (`EKAutomorphisms.psi3_hWord_source`).
9. **Step before (2.26), p. 21 [G].** One transformation is omitted when ψ₃ is applied to (2.5);
   the step needs ψ₃(e_n) = (−1)^{C(n+1,2)} ψ₂(e_n) (`ErrataChecks.psi3_e`), after which ψ₃ applied
   to (2.5) gives `ErrataChecks.psi3_relation_2_5`; (2.26) then follows by applying ψ₂
   (`ErrataChecks.eq_2_26`).
10. **(3.4), p. 23 [F→T].** False as printed: `det M₂ = −1`
   (`EKDeterminant.equation_3_4_counterexample`), for every ordering
   (`EKDeterminant.counterexample_under_every_order`). Correct formula, every d:
   `det M_d = (−1)^{(p(d)−sc(d))/2} · Π_{λ=λᵀ} (−1)^{ℓ(w_λ)}`, where sc(d) counts self-conjugate
   partitions (`EKDeterminantCorrected.det_M`). The printed formula holds exactly when
   `(p(d)−sc(d))/2` is even (`EKDeterminantCorrected.printed_iff`).
11. **Example 3.2, p. 24 [M].** The printed exponents of the cable signs use C(3,2) where C(2,2) is
   meant; the signs agree, and every printed contribution and total is correct
   (`EKMore.ex32_table`, `EKMore.ex32_column_sums`).
12. **"f_n = ±m_n", p. 25 [F→T].** It fails for n = 7: (e₇, m₇) = 5 while (e₇, f₇) = 1, so f₇ is
   not a multiple of m₇ (`EKRest.f_seven_ne`); indeed m₇ = 4f₄₃ + 8f₅₂ + 5f₇, so f₇ and m₇ are
   linearly independent (`EKMore.m_seven_f_expansion`, `EKMore.f_seven_m_seven_independent`). It holds for n = 1 and every even n, with the sign
   the coefficient of h_n in e_n, as stated (`EKRest.f_eq_smul_m`, `EKRest.e_coefficient`), and
   for n = 3, 5 (`EKRest.f_three`, `EKRest.f_five`). The conclusion drawn from it (the f_{2k} are
   primitive) holds (`EKRest.f_primitive`).
13. **Proof of Prop 3.4, p. 26 [G, M].** "Only λ = (k+1, 1^{m−1}) and (k, 1^m) yield nonzero
   results" fails for odd k ≥ 3: (p₃h₁, e₂₂) = (h₁p₃, e₂₂) = 2
   (`EKComplete.prop_3_4_support_false`), and (p₅h₁, e₃₃) = 2, (h₁p₅, e₃₃) = −2
   (`ErrataChecks.prop_3_4_support_false_k5`). The printed values are wrong in sign:
   (p₄h₁, e₅) = (h₁p₄, e₅) = −1 (`EKComplete.prop_3_4_values_false_k4`); for k = 1 both
   pairings are 0 (`EKComplete.prop_3_4_values_false_k1`). Prop 3.4 holds
   (`EKCenterPower.center_iff`).
14. **Uniqueness of Schur functions, p. 29 [G].** The cited argument relies on the false equality
    in item 5. The characterization of s_λ by properties (1)–(2) holds
    (`EKComplete.schur_characterisation`, `EKComplete.schur_existsUnique`).
15. **Prop 3.10 proof, p. 29 [G].** The intersection claimed to be one-dimensional has dimension
    ≥ 2 at λ = (3,3): it contains the independent s₃₃ and s₄₁₁
    (`ErrataChecks.prop_3_10_intersection`, `ErrataChecks.prop_3_10_not_one_dim`). Prop 3.10 holds (`EKClosureComposition.proposition_3_10`).
16. **Lemma 3.11 proof, pp. 29–30 [G, M].** The same one-dimensionality failure occurs at
    λ = (2,2,2) (`ErrataChecks.lemma_3_11_printed_intersection`,
    `ErrataChecks.lemma_3_11_not_one_dim`); the indices of the intersection are swapped
    (ψ₁ψ₂(s_λ) ∈ H_{≥λᵀ} ∩ E_{≥λ}: `ErrataChecks.psi12_schur_mem_corrected`,
    `ErrataChecks.lemma_3_11_printed_not_mem`), and the first display has `h_μ` for `e_μ`
    (`ErrataChecks.lemma_3_11_first_display`). The lemma
    holds (`EKFinalClosure.lemma_3_11`).
17. **Proof of Cor 3.12, p. 30 [G].** Applying ψ₁ψ₂ to (3.10) does not give the second equation of
    (3.14), because ψ₁ψ₂ does not send m_μ to ±f_μ: ψ₁ψ₂(m₃) = −h₁₁₁ + h₂₁ − h₃ while
    f₃ = h₁₁₁ + h₂₁ − h₃ (`EKComplete.cor_3_12_proof_gap`). (3.14) holds
    (`EKFinalClosure.cor_3_12_second`).
18. **p. 31, ⟨s_λ, s_λ⟩ = (−1)^{½ s*(2λ)} [M].** For λ = (1,1), s*(2λ) = 1, so the exponent is
    not an integer (`EKComplete.printed_exponent_not_integer`). The correct norm is
    (−1)^{s*(2λ)} (`EKComplete.norm_schur_spin`, `EKComplete.twiceSpinMax_double`).
19. **(3.8) [M].** The same label swap as item 20 (`EKRskBijection.printed_codomain_obstruction`); the
    sign identity holds (`EKRskSign.thm_3_7_sign`).
20. **(4.3) and Example 4.5 [F→T].** The printed codomain (cont P = μ, cont Q = ρ) is impossible
    when μ ≠ ρ (`EKRskBijection.printed_codomain_obstruction`,
    `EKRskBijection.ex45_printed_obstruction`). With the contents swapped, Thm 4.3 holds
    (`EKRskBijection.rsk_bijective`). (4.4) holds as printed.
21. **§5.2, p. 39: "all are monic and with constant coefficient 1, so their roots are units"
    [F→T].** The factor q in degree 2 has root 0, which is not a unit, and q − 1 has constant term
    −1 (`EKGeneralQ.minimal_polynomials_counterexample`); neither is palindromic, contrary to "all of
    the polynomials are palindromic" (`EKFinal.q_and_q_sub_one_not_palindromic`). The printed factors
    and multiplicities are otherwise correct: determinants in degrees ≤ 6 (`EKGeneralQ.det_gram2`,
    `EKGeneralQ.det_gram3`, `EKRest.det_gramH_four`, `EKFinal.det_gram_five`, `EKFinal.det_gram_six`);
    every printed factor through degree 7 is irreducible over ℚ, and the factors marked as roots of
    unity are the cyclotomic polynomials (`EKFinal.printed_cyclotomic`, `EKFinal.cyclotomic_facts`, `EKFinal.linear_irreducible`,
    `EKFinal.f6_irreducible`, `EKFinal.f18_irreducible`, `EKFinal.f50_irreducible`,
    `EKFinal.f102_irreducible`).
22. **§5.2, p. 40: "this determinant is monic in q" [F→T].** In degree 3 the Gram determinant is
    −q⁵(q−1)(q+1) (`EKGeneralQ.det_gram3_not_monic`). In every degree the leading coefficient is
    the sign of α ↦ α^rev on compositions (`EKGeneralQ.gram_det_leadingCoeff`); the degree is
    2^{n−2}(n² − 3n + 4) − 1 as in (5.1)–(5.2) (`EKMore.gram_det_natDegree_closed`).

## [EKL] A. P. Ellis, M. Khovanov, A. D. Lauda, *The odd nilHecke algebra and its diagrammatics*, arXiv:1111.1320v1

1. **(2.18), middle expression [M].** The denominator q^a − q^{−a} should be q^i − q^{−i}; as
   printed the expression is wrong at a = 2 (`EKLGaps.eq_2_18_printed_false`). Corrected, for all a:
   `EKLGaps.eq_2_18`.
2. **(2.19) [M].** The exponent is q^{2ℓ(σ)}, not q^{ℓ(σ)} (`EKLSectionTwo.qrkPol_eq`); the
   printed form is refuted by `EKLSectionTwo.printed_qrk_quotient_false`.
3. **Proof of Prop 2.2, p. 8 [M].** The leading term of ε_α is x^{αᵀ} with coefficient ±1, not
   x^α with coefficient 1 (`EKLSectionTwo.printed_leading_term_false`; correct leading term:
   `EKLSectionTwo.word_leading`).
4. **(2.34) [M].** The index k is unbound; with h_{m−j} the formula holds
   (`EKLSectionTwo.complete_last`).
5. **(2.43) [F→T].** The selector w = u⁻¹ should be w = u. The printed form holds for a = 2 and fails for
   every a ≥ 3 (`EKLGaps.printed_2_43_rank_two`, `EKLGaps.printed_2_43_false`); corrected:
   `EKLGaps.eq_2_43`, `OddSchubertAction.action_self`, `OddSchubertAction.action_same_length_distinct`.
6. **(2.49)–(2.51) [M, G].** In (2.49) and in the second equality of (2.50) the sums must start
   at k = 0; f = 1 is a counterexample (`EKLSectionTwo.eq_2_49_printed_fails`,
   `EKLSectionTwo.eq_2_50_printed_fails`; corrected: `EKLSectionTwo.eq_2_49_sum_from_zero`,
   `EKLSectionTwo.eq_2_50_sum_from_zero`). The step "h·x_{a−1}^i ∈ H_{a−1}" in the proof of
   (2.51) is false for H of (2.46) (`EKLGaps.eq_2_51_step_false`); (2.51) holds (`EKLSectionTwo.eq_2_51`).
7. **Prop 2.15, the centre of OΛ_N and ONH_N [F→T].** The printed description (symmetric
   polynomials in x₁², …, x_N²) is correct exactly for even N (`CenterCorrected.printed_iff_even`,
   `CenterCorrected.printed_iff_even_nilHecke`). For N = 3, x₁x₂x₃ is central but not of that form
   (`NilHeckeCenter.kernel_center_counterexample`). The first step of the proof ("doing this for
   each j separately") fails: xᵃ commutes with every xⱼ iff |a| − aⱼ is even for all j, which for
   odd N also allows all exponents odd (`CenterPoly.mem_center_iff`). Corrected statement, every
   N ≥ 2: the centre of OΛ_N is {a + x₁⋯x_N·b : a, b symmetric in x₁², …, x_N²}, with b = 0 for
   even N, and the centre of ONH_N is its image under the dot inclusion
   (`CenterCorrected.center_oddSymmetric`, `CenterCorrected.center_nilHecke`).
8. **Lemma 2.18 (OWL) for an arbitrary reduced word of w₀ [F→T].** Counterexample in 5 variables,
   word `[0,1,0,3,2,1,0,3,2,1]`: `OwlDirect.owl_trichotomy_false`. The proof reorders the D_a
   termwise; distant commutations preserve OWL, but a single braid move need not
   (`OwlBraid.braid_transport_false`). Corrected statement, every N ≥ 2 (letters 0, …, N−2): OWL
   and the kernel identity (2.64) hold for every word in `OwlGeneral.OwlClass`
   (`OwlGeneral.owl_general`, `OwlGeneral.left_kernel_owl_class`). This class is built from the
   empty word by (i) prepending the chain (N−2, N−3, …, N−2−r) to a class word on the top r+1
   strands, and (ii) the flip i ↦ 2N−3−r−i of the top r+1 strands, and is closed under distant
   commutations. Its words are reduced words of w₀ (`OwlGeneral.owlClass_reduced_longest`). It
   contains the printed block word, which is the case used for (2.64)
   (`OwlGeneral.blockClass_owlClass`, `OmissionCanonical.trichotomy`), and it is strictly larger
   (`OwlGeneral.not_blockClass_stageExample`). Whether OWL holds for words outside this class is
   open. (2.64), Cor 2.22 and Cor 2.23 are proved.
9. **Proof of Lemma 2.18, p. 17 [M].** "D′_a = (−1)^{C(a,3)} D_a" is false at a = 3, where
   D′₃ = D₃ (`EKLGaps.owl_Dprime_printed_false`, `EKLGaps.owl_Dprime_printed_iff`); the correct sign
   is (−1)^{C(a,4)} (`EKLGaps.owl_Dprime_sign`). The line "Explicitly, D_a = …" should read D′_a; as
   printed it fails at a = 4 (`EKLGaps.owl_explicit_false`, `EKLGaps.owl_explicit_iff`).
10. **(2.63) [M].** In the case ℓ = j − i the word should read s_{i+1}⋯s_{j−1}s_{i,j}; the identity
   holds for all g, h ∈ OΛ_a (`EKLSectionTwo.eq_2_63`).
11. **At (2.65) [M].** An extra staircase factor in the leftmost argument; correct:
   `OddSymmetrizer.S_eq_self`.
12. **Remark 2.27, (2.73)–(2.74) [G].** η_α is not defined in [EK], and ψ₃ does not act diagonally
    on Schur functions (`EKLSectionTwo.psi3_not_diagonal`). With η_λ defined by R(s_λ) = η_λ s_λ
    for the anti-involution R fixing every h_n (`EKLSectionTwo.reverse_sK`), both identities hold
    as printed, in OΛ and in every OΛ_a (`EKLSectionTwo.left_vertical_pieri`,
    `EKLSectionTwo.left_horizontal_pieri`).
13. **Remark 2.28, (2.76) and the h-expansions [F→T].** s₂₂ = −ε₂₂ + ε₃₁ + 2ε₄ for a ≥ 4
    (`EKLSectionTwo.schur_two_two`), not ε₂₂ + ε₃₁ − 2ε₄, nor its negative
    (`EKLSectionTwo.printed_schur_two_two_false`, `…_false_neg`); h₂₂ = ε₂₂ + 2ε₂₁₁ + ε₁₁₁₁ and
    h₃₁ = ε₃₁ + ε₁₁₁₁ (`EKLSectionTwo.complete_two_two`, `EKLSectionTwo.complete_three_one`; the
    printed forms are refuted by `EKLSectionTwo.printed_complete_determinant_false`). The
    conclusions of the Remark hold (`EKLSectionTwo.schur_ne_elementary_determinant`,
    `EKLSectionTwo.schur_ne_complete_determinant`, `EKLSectionTwo.elementary_four_not_mem`).
14. **(3.14), middle expression [M].** Σ_ℓ j should be Σ_ℓ ℓ; as printed it fails at a = 4
   (`EKLGaps.eq_3_14_printed_false`). Corrected: `EKLGaps.eq_3_14`.
15. **(3.49) [M].** The factor x_{a−2}^{a−1} should be x_{a−1}^{a−2}: for every a ≥ 3, ψσ(x^δ) is not
   a multiple of the printed monomial (`EKLGaps.eq_3_49_printed_false`); corrected:
   `OnhReflection.eq_3_49`.
16. **(3.51) [F→T].** `D_a = σ(D_a)` holds, but `ψ(D_a) = (−1)^{binom(a,4)} D_a` (and likewise
    for `ψσ(D_a)`), not `(−1)^{binom(a−1,4)}`; the printed sign fails at `a = 4`
    (`OnhReflection.eq_3_51_false`, `OnhReflection.eq_3_51_printed_false`). Corrected:
    `OnhReflection.eq_3_51`. (3.52)–(3.54) hold as printed.
17. **(4.26)–(4.27), "big odd shuffle" [F→T].** The printed coefficient `(−1)^{m(j+1)}` is wrong
    from `j = 3` on; the formula fails for `m = 0, k = 7` (`ShuffleLemma.big_shuffle_false`).
    The correct coefficient is `(−1)^{binom(j,2) + (m+1)(j+1)}`, for all `m` and odd `k`
    (`ShuffleLemma.big_shuffle`). The displayed (4.26) fails in the same way
    (`EKLGaps.eq_4_26_printed_false`, `EKLGaps.eq_4_26_printed_tilde_false`; corrected:
    `EKLGaps.eq_4_26`). Lemma 4.4, Props 4.5–4.7 and Lemmas 4.8–4.9 hold as printed.
18. **(4.52) [M].** X^{a,1}_{(1^r)} ≡ a(a−r) + C(a−r+1,2) holds only mod 2
    (`EKLMisc.signX_col_mod_two`, `EKLMisc.signX_col_exact`; the integer equality fails:
    `EKLMisc.eq_4_52_false`), and X^{a,1}_{(1^a)} is even, not 1 (`EKLMisc.signX_col_self_even`,
    `EKLMisc.neg_one_pow_signX_col_self`). Lemma 4.14 and Thm 4.15 are unaffected.
19. **Proof of Thm 4.16 [G].** It appeals to ONH_a ≅ Mat(OΛ_a) without the rank argument needed;
    `ThickDecomposition.thm_4_16` supplies it by a graded trace count.
20. **p. 44 [M].** "The ε_λ form a basis of OΛ_a just like the h_λ": in OΛ_a the family of all h_λ
    is linearly dependent (h_3 = h_1³ for a = 2: `EKLMisc.complete_parts_not_basis`). The statement
    holds for OΛ (`EKIntegralBases`) and, for OΛ_a, for the ε_λ with parts ≤ a
    (`EKLMisc.elementary_basis`).
21. **Lemma 5.1, (5.4) [F→T].** For the action of Corollary 2.14 (on OPol_a as a right
    OΛ_a-module) the printed matrix is not the matrix of φ(x̃_1) on B_β: at a = 2, β = 0 it gives
    x_1² = x_1ε_1 + ε_2, whereas x_1² = x_1ε_1 − ε_2 (`Cyclotomic.lemma_5_1_printed_false`). The
    first column is (−1)^{j(|β|+1)+1} ε_j (`Cyclotomic.lemma_5_1`). The display in the proof holds
    with left coefficients (`Cyclotomic.lemma_5_1_left`).
22. **Proof of Prop 5.2, (5.8)–(5.9) [M].** In (5.8) the exponent C(N−a,2) should be C(N−a+2,2)
    (`Cyclotomic.eq_5_8_false`, `Cyclotomic.choose_two_parity`); in the second case of (5.9) the
    sign is −(−1)^{a(N−a+1)} (`Cyclotomic.eq_5_9_false`, `Cyclotomic.eq_5_9_top`); the corrected (5.8)
    step is `EKLGaps.eq_5_8`, `EKLGaps.eq_5_8_step`. With the matrix (5.4) as printed, the inductive
    claim (M^{N−a+1}v)_j = (−1)^{C(N−a+j+1,2)} f_{j,N−a} already fails for N = a = 2
    (`EKLGaps.prop_5_2_claim_base_false`; see item 21). Prop 5.2 holds
    (`Cyclotomic.prop_5_2`, proved by a different route). In right coordinates, the ideal
    generated by the entries of x̃_1^N is the image of ⟨h_m : m > N−a⟩ under the w_0-reversal
    (`Cyclotomic.entryIdeal_eq_rev`).
23. **Proof of Prop 5.4 [G].** It uses without proof that OH_{a,N} is a free ℤ-module. Prop 5.4
    holds, and OH_{a,N} is free of rank C(N,a) (`OddGrassmannSchur.proposition_5_4`,
    `OddGrassmannSchur.finrank_OH`).
24. **(6.1) [M].** The grading shifts of the summands are C(a,2) − 2|ℓ| (the exponents of [a]!),
    not a − 1 − 2|ℓ|; the printed shifts fail at a = 3 for either sign convention
    (`OddCategorification.eq_6_1_printed_false`). Corrected: `OddCategorification.eq_6_1_K0`.
25. **§6, p. 47: "OH_{a,N} is graded local" [F→T].** Over ℤ a connected graded ring with
   augmentation ε has the distinct maximal homogeneous ideals ε⁻¹(pℤ), p prime
   (`EKLGaps.Augmented.isMax_iff`), so OH_{a,N} is not graded local, in any rank
   (`EKLGaps.oh_not_gradedLocal`, `EKLGaps.ohZero_not_gradedLocal`, `EKLGaps.ohOne_not_gradedLocal`).
   It is graded connected (`Cyclotomic.ohConnected`), which is what the K_0 argument needs
   (`Cyclotomic.finrank_K0Cyc`), and after base change to any field it is graded local
   (`EKLGaps.oh_baseChange_gradedLocal`).
26. **Minor slips (partly *textual*).** (5.1): "a_i a_j = a_j a_j" should read "a_i a_j = a_j a_i"; Lemma
    3.3 is an identity in ONH_{a+1}, not ONH_a; in the proof of Lemma 5.1 the sum runs to j = a;
    §1.1 speaks of the negative half of U_q(sl_2) where the abstract and §6 (and (6.3)) use the
    positive half; the idempotent 1_n in (6.2) is stray. (Lemma 3.3 in ONH_{a+1}:
    `ErrataChecks.lemma_3_3_in_ONH_succ`; the Lemma 5.1 sum: `Cyclotomic.lemma_5_1_left`.)

## [E] A. P. Ellis, *The odd Littlewood–Richardson rule*, arXiv:1111.3932v1

1. **§1, interpretation (1) (*textual*, M).** S_{k×ℓ} should be S_{k+ℓ}.
2. **(2.4) [M, *textual*].** "if a+b if odd" should read "if a+b is odd".
3. **§2.1 and (2.9): ψ₃ is used in two incompatible senses [F→T].** The antipode formula
   S = ψ₁ψ₂ψ₃ holds for [EK]'s super anti-involution ψ₃ (`EKAntipode.antipode_identities`). For
   that ψ₃, ψ₁ does not commute with ψ₃ (`OddLRMisc.psi1_psi3_not_commute`; ψ₂ does:
   `OddLRMisc.psi2_psi3_comm`), (2.9b) fails (`EKLSectionTwo.psi3_not_diagonal`), and ψ₃ *is* a
   coalgebra homomorphism, contrary to the aside (`OddLRMisc.psi3_coproduct`). For the ordinary
   anti-involution R with R(h_k) = h_k, both ψ₁ and ψ₂ commute with R
   (`OddLRMisc.reverse_psi1_comm`, `OddLRMisc.reverse_psi2_comm`), R is not a coalgebra
   homomorphism (`OddLRMisc.reverse_not_coalgebra`), and (2.9b) holds
   (`OddLRMisc.reverse_sK_source`, with the sign bridge `OddLRMisc.eta_eq`). But S ≠ ψ₁ψ₂R: S(h₁²) = −h₁² while
   ψ₁ψ₂R(h₁²) = h₁² (`EKAntipode.S_square_word`, `OddLRGaps.antipode_ne_psi12_reverse`). Correction:
   keep [EK]'s ψ₃ for the antipode, and use R in "both ψ₁, ψ₂ commute with ψ₃", in (2.9b), in
   Remark 4.10, and in the §4.2 remark that ψ₁ψ₂ and ψ₃ give c^λ_{μν} when μ or ν is a row or
   column (the left Pieri rules: `EKLSectionTwo.left_vertical_pieri`,
   `EKLSectionTwo.left_horizontal_pieri`). (2.9b) is attributed to [EK] §3.3,
   which states only the ψ₁ψ₂ half (Lemma 3.11).
4. **Proof of Thm 3.8, last paragraph [M].** The triangularity is with respect to the
   lexicographic order on λᵀ, as announced at the start of the induction ("μ … lexicographically
   greater than or equal to λ" should read μᵀ ≥ λᵀ); with row-lex the step fails
   (`OddLREliminationControls.row_lex_variant_fails`). The displayed product should be a product
   of column Schur functions s_{(1^{λᵀ_1})}⋯s_{(1^{λᵀ_r})}, not of row Schur functions. Thm 3.8
   holds (`OddLRThm38.thm38`, via `OddLRElimination.eliminate`, `OddLRElimination.strip_lex`; in
   every rank with `OddLRThm38.sK_eq_sp` and `SmallRank.conjecture_5_3_small`).
5. **Cor 3.9 [G].** It is stated without proof and does not follow from Thm 3.8 alone; the paper
   also uses without proof that the tableau words form a basis of ℤPl_n. Both hold, in
   every rank (`OddLRPlactic.tableauBasis`, `OddLRExamples.cor39_all`). Lemma 4.7, whose proof reads
   coefficients in ℤPl_n, depends on Cor 3.9; it holds, along the printed route
   (`OddLRExamples.lemma_4_7_plactic`) and independently of Cor 3.9 (`OddLRRule.lemma_4_7`), and
   Thm 4.8 holds (`OddLRRule.thm_4_8`).
6. **§4.2, "sign(S) = sign(Ŝ) = N^<(Ŝ)" [M].** Read (−1)^{N^<(Ŝ)} (`OddLRTableau.SkewTableau.sign`); for the tableaux of Example 4.9,
   N^< = 7 and 6 (`ErrataChecks.sign_display_printed_false`).
7. **Def 4.11(3), the index range [F→T].** The range 1 ≤ i < j < n must be 1 ≤ i ≤ j < n, and
   a₀₀ = 0 is needed. With the printed definition, for n = 2, λ = (2,2), μ = (2), ν = (1,1), the
   point (0; 2,0; 0,1,1) is an LR triangle (`OddLRHive.cex_mem_printed`), while the corrected set is
   empty (`OddLRHive.corrected_empty`). Lemma 4.12, Thm 4.15 and (4.14) fail as printed
   (`OddLRHive.printed_lemma_4_12_fails`, `OddLRHive.printed_phi_not_subset`,
   `OddLRHive.printed_4_14_fails`). With the correction they hold (`OddLRHive.lemma_4_12`,
   `OddLRHive.phi_bijOn`, `OddLRHive.eq_4_14`); the hive formula (4.20) holds as printed
   (`OddLRHive.eq_4_20`).
8. **Def 4.11 [M].** In ν_i = Σ_{q=i}^{k} a_{i,q} the index k is unbound; read n
   (`OddLRHive.IsLRTriangle`).
9. **Remark after (4.18) [M].** "(R) makes the parenthesized term non-negative" holds only for
   j > i (`ErrataChecks.eq_4_18_term_nonneg`); for i = j it can be negative on a hive
   (`ErrataChecks.hexH_isHive`, `ErrataChecks.eq_4_18_diagonal_term_neg`).
