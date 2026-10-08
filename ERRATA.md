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

## [EQ] A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2

In progress (Thm 3.18 and Thm 4.17 are proved; see the README); strands are numbered from `0` in Lean.

1. **§2.1, the twist of `U⁺ ⊗ U⁺` [F→T].** With the displayed twist `(b₁⊗b₂)(b₁'⊗b₂') = v^{|b₂||b₁'|} b₁b₁' ⊗ b₂b₂'`,
   `v = √−1`, no algebra map `r` with `r(E) = E⊗1 + 1⊗E` exists, on `u⁺` or on `U⁺`
   (`EQQuantum.printed_twist_no_coproduct`, `small_printed_twist_no_coproduct`; `(E⊗1 + 1⊗E)² = (1 + t) E⊗E` for twist
   `t`, `EQQuantum.tw_sq`). Such an `r` exists iff the twist is `−1`, i.e. `(−1)^{|b₂||b₁'|}`
   (`EQQuantum.twisted_coproduct_exists_iff`, `small_twisted_coproduct_exists_iff`); with it, (2.1) and (2.2) hold as printed
   (`EQQuantum.eq_2_1`, `eq_2_2`, `rU`, coassociative, `rU_coassoc`), `u⁺ ↪ U⁺` is a map of twisted bialgebras
   (`EQQuantum.rU_iota`), and `r` is the specialisation at `q = √−1` of the q-bialgebra of [EKL] §6 (braiding `q^{−2} ↦ −1`;
   `EQQuantum.rU_mapDP`). Equivalently: Lusztig's `v^{(|b₂|,|b₁'|)}` with `(E,E) = 2`, or the Koszul sign for the parity
   `|E^{(n)}| = n`.
2. **§2.1, "[a+b choose a] is zero if a+b is even" [F→T].** False: at `q = √−1`, `[4 choose 2] = 2`
   (`EQQuantum.printed_zero_claim_false`). Correct: `[a+b choose a]_{√−1} = 0` iff `a` and `b` are both odd
   (`EQQuantum.evI_qBinom_eq_zero_iff`), with the closed form `EQQuantum.evI_qBinom`.
3. **§3.4, basis `B'_n` before (3.37)–(3.38) [F→T].** The printed basis
   `B'_n = {x^a 1_z : 0 ≤ a_i ≤ n − i}` together with the claim `d(x_i^{n−i} 1_z) = 0` does not give a
   `d`-stable span for even `n`: the span of the printed monomials is `d`-stable iff `n = 0` or `n` is odd
   (`EQZn.staircase_span_stable_iff`); for `n = 2`, `d(x_1 1_z) = x_1² 1_z − x_1x_2 1_z`. The range printed in
   Appendix A.2, `0 ≤ a_i ≤ i − 1`, is the correct one: its span `U_n` is `d`-stable for every `n`
   (`EQZn.dAlpha_mem_Hrev`), `B'_n` is a basis of `Z_n` as a right `OΛ_n`-module (`EQZn.zn_right_basis`),
   `Z_n ≅ U_n ⊗ OΛ_n` as in (3.38) (`EQZn.eq_3_38`), and Prop 3.16 (1) holds (`EQZn.prop_3_16_1`).
4. **§3.4, Cor 3.15 and the remark after it [F→T].** With null-homotopies of dg `OPol_n`-modules in the sense of
   §2.2 (module maps of degree `−1`), the identity of `OPol_n(α)` is never null-homotopic, for any `n` and `α`
   (`EQFix.cor_3_15_dg_false`, also without the grading: `EQFix.cor_3_15_superLinear_false`, `cor_3_15_linear_false`), and
   likewise for `Z_n` (`EQZn.zn_not_contractible`), contrary to "(considered as a left `OPol_n`-module)" in the remark. What
   holds is the statement for the underlying complex: `∂/∂x_i` is a null-homotopy of the identity of the complex
   `OPol_n(α)` when `α_i = 1` (`EQSkewDifferential.cor_3_15`).
5. **§4.1, the reduced expression for `w_{a,b}` [M].** The printed word
   `(s_b s_{b−1} ⋯ s_1)(s_{b+1} s_a ⋯ s_2) ⋯ (s_{a+b−1} s_{a+b} ⋯ s_a)` has index slips (the second and last
   factors should read `s_{b+1} s_b ⋯ s_2` and `s_{a+b−1} s_{a+b−2} ⋯ s_a`; `s_{a+b}` does not exist on `a + b`
   strands). The formalization uses the reversed word of EKL (3.41), `EQThick.crossEQ`; a different reduced
   expression changes `∂_{w_{a,b}}` only by a sign, and Prop 4.2 is linear in it.
6. **§4.1, `∂_{w_0} f = w_0(f) ∂_{w_0}` for `f ∈ OΛ̃_n` [F→T].** With Ellis–Qi's plain permutation action `w_0` this
   fails: in rank 2, `∂ ẽ_1 = ẽ_1 ∂` while `w_0(ẽ_1) = −ẽ_1` (`EQThick.DElem_mul_poly_printed_false`). Correct: for `f`
   of parity `k`, `∂_{w_0} f = (−1)^{binom(n,2) k} w_0(f) ∂_{w_0}` (`EQThick.DElem_mul_poly`). The same parity-dependent
   sign is the correct form of the identity cited from EKL (2.64) in the proof of Lemma 2.18; Lemma 2.18 itself
   holds (`EQZn.eqIdempotent_mul_polyElem`), and so does the consequence `e_n f e_n g e_n = e_n f g e_n`
   (`EQThick.thick_mul_thick`).
7. **§4.1, `e_n x_1 ⋯ x_k e_n = ẽ_k e_n` [F→T].** Off by the sign `(−1)^{binom(k,2)}`; false for `n = k = 2`
   (`EQThick.convenient_relation_printed_false`). Correct: `e_n x_1⋯x_k e_n = (−1)^{binom(k,2)} ẽ_k e_n`
   (`EQThick.convenient_relation`). For `k ≤ 1`, the case used in Prop 4.2, the printed form is correct.
8. **§4.1, the slider relation [F→T].** The printed factor `(−1)^{binom(s,2)}` (with the right-leg coupon drawn above
   the left) is wrong: the printed relation fails in `ONH_3` for `a = 2`, `b = 1`, `s = 2`
   (`EQThick.slider_printed_false`). Correct: moving `ẽ_s` through a splitter gives
   `Σ_{l=0}^{s} (−1)^{a l} (ẽ_{s−l} ⊗ ẽ_l)` with the left coupon above the right and no further sign (`EQThick.slider`,
   from the coproduct formula `EQThick.elementary_coproduct`). For `s ≤ 1` the two agree.
9. **§4.2, the differential on thick diagrams [textual].** In Prop 4.2 and Cor 4.3, `d` is the differential
   of Lemma 2.2 on idempotent truncations, `e d(−)` with `e` the idempotent at the top of the diagram (as the
   proof's first step indicates), not the restriction of the differential of `ONH_n`: with the latter the
   printed formulas fail already in rank 2 (`EQThick.dONH_DElem_ne_thickD_rank_two`). With `e d(−)` they hold
   as printed (`EQThick.prop_4_2_splitter`, `prop_4_2_merger`, `cor_4_3_split`, `cor_4_3_merge`).
10. **§4.3, Lemma 4.5 and the formula for `s̃̂_λ` after it [F→T].** With the printed definitions of `s̃̂_λ` and `ŝ_λ`
   (via `η^n_λ`), the horizontal arrows of Lemma 4.5 and the displayed `s̃̂_λ = (−1)^{Σ_{i<j} λ_iλ_j} ∂_{w_0}(x^λ x^δ)` fail
   for `n = 2`, `λ = (1)` (`EQZab.lemma_4_5_bottom_false`, `lemma_4_5_top_false`, `hat_formula_false`). They hold after
   multiplying by `(−1)^{binom(n+1,4) + Σ_j λ_j (n−j)}` (`EQZab.lemma_4_5_bottom`, `lemma_4_5_top`, `twistedHat_eq_D`); the
   vertical arrows are correct (`EQZab.untwistedHat_eq_theta`, `EQSchur.twisted_eq_theta_untwisted`).
11. **§4.3, Prop 4.13 (1) [F→T].** For a composition `(a_1, a_2)` with `a_1, a_2 ≥ 1` the printed set (with `λ_i` in an
   `(a_1 + ⋯ + a_{i−1}) × a_i` box and the product ending at `λ_{k−1}`) reduces to `{z}`, which does not span `Z_{a_1,a_2}`
   (`EQZab.prop_4_13_one_printed_false`). For two blocks the correct basis is `{s̃_μ(y) z : μ ∈ Par(b,a)}` of Cor 4.8
   (`EQZab.zab_span_twisted`, `zab_indep_twisted`), with `d`-stable span (`EQZab.cor_4_8_stable_twisted`). For `r` blocks
   the correct basis of `OΛ̃_{a_1} ⊠ ⋯ ⊠ OΛ̃_{a_r}` over `OΛ̃_n` is `{s̃_{λ_1}(X_1) ⋯ s̃_{λ_r}(X_r)}`, `X_i` the `i`-th block of
   variables and `λ_i` in an `a_i × (a_1 + ⋯ + a_{i−1})` box (`EQBlocks.prop_4_13_one_span`, `prop_4_13_one_indep`).
12. **Appendix A.1, proof of Prop A.3 [G].** Two claims in the proof are false, although Prop A.3 holds: (i) "for Lima
   partitions the odd Littlewood–Richardson coefficients equal the even ones" fails for the Lima partitions `μ = ν = (2,2)`,
   with odd coefficient `−1` and even coefficient `1` at `λ = (4,3,1)` (`EQLima.printed_oddLR_eq_evenLR_fails`); in
   particular the coefficients `a_μ` in (A.1) are not all non-negative; (ii) "Lima Schur functions pairwise commute" fails in
   `OΛ` for `(4,4,2,2)` and `(2,2)` (`EQLima.lima_schur_not_comm`). Their classes do commute in `H(OΛ)`
   (`EQLima.oddLR_comm_of_lima`, `HQ.instCommRing`), (A.1) holds in cohomology with leading coefficient `±1` and lower terms
   in dominance order (`EQLima.tri_mul`), and Prop A.3 follows for both generating sets
   (`EQLima.prop_A_3_columns`, `prop_A_3_rows`; the generators are indexed by `k ≥ 1`, since `s_∅ = 1`).
13. **Appendix A.2, the urn description of `U_n` [M].** A factor `x_i^{a_i}` with `i ≡ a_i + 1 (mod 2)` is a full urn only
   if `a_i ≥ 1`; `x_i^0` with `i` odd is not an urn (nothing can be removed) (`EQApp.notMem_uRemovable_of_zero`). With this
   reading `U_n` is a direct sum of hypercube complexes (`EQApp.uDecompEquiv_dU`), the initial vectors are the `x^a` with
   `a_i ∈ {0} ∪ {a ≤ i − 1 : a ≡ i mod 2}` (`EQApp.init_iff`, matching the printed `n = 5, 6` cases, `init_five`), and
   `H(U_n) = 0` for `n ≥ 2` (`EQApp.homology_U_subsingleton`).
14. **Appendix A.3, the cohomology of `V_{a,b}` for `a` odd [F→T].** The printed claim `H(V_{a,b}) = 0` for `a` odd fails when
   `b` is even: the class of `s_{(a^b)} 1_z` is nonzero (`EQApp.homologyVT_rectangle_ne_zero`); the smallest case is
   `a = 1`, `b = 2`, where `H ≅ ℤ [s_{(1,1)} 1_z]`. Inside the `b × a` box the rectangle has no addable box and its only
   removable box has content `a − b`, which is odd. Correct: for `a` odd, `H(V_{a,b}) = 0` if `b` is odd
   (`EQApp.homologyVT_odd_odd`), and for `b` even it has basis the partitions whose rows `2k, 2k+1` are equal and odd
   (`EQApp.homologyVT_odd`); for `a` even the printed Lima description holds (`EQApp.homologyVT_even`).
15. **Appendix A.4, definition of slash cohomology [M].** As printed,
   `H_{/k}(V) = Ker(d^k)/(Im(d^{p−k−1}) + Ker(d^{k+1}))` is always zero since `Ker d^k ⊆ Ker d^{k+1}`
   (`EQPdg.printedSlash_subsingleton`). The cited definition of Khovanov–Qi,
   `Ker(d^{k+1})/(Im(d^{p−k−1}) + Ker(d^k))`, is used (`EQPdg.SlashCohomology`); with it (A.4) holds
   (`EQPdg.slash_shiftV_pos`, `slash_shiftV_zero`).
16. **Appendix A.4, `d(e_k)` and `d(h_k)` [M].** The printed `d(e_k) = e_1 e_k − e_{k+1}` and
   `d(h_k) = h_{k+1} − h_1 h_k` miss the factor `k + 1` (`EQPdg.pd_esymm_printed_false`,
   `pd_hsymm_printed_false`; the printed forms hold iff `k e_{k+1} = 0`, resp. `k h_{k+1} = 0`). Correct:
   `d(e_k) = e_1 e_k − (k+1) e_{k+1}` and `d(h_k) = (k+1) h_{k+1} − h_1 h_k` (`EQPdg.pd_esymm`, `pd_hsymm`), consistent
   with the printed `d(s_λ)` (`EQPdg.pd_schur`).
17. **§4.3, the hat Pieri rule (4.19) [F→T].** The printed sign `(−1)^{binom(n−1,2) + |λ/i|}` is wrong: for `n = 2`,
   `λ = ∅`, `ẽ_1 = −s̃̂_{(1)}` (`EQZab.hat_pieri_printed_false`). Correct:
   `ẽ_1 s̃̂_λ = Σ_{μ = λ + □_i} (−1)^{binom(n,2) + |i/λ|} s̃̂_μ` (`EQZab.hat_pieri_partition`; for every exponent vector,
   `EQZab.hat_pieri`). The hat SZ relation (4.18) holds as printed (`EQZab.hat_sz`).
18. **§4.3, the differential of `ŝ_λ` (4.20) [F→T].** The printed formula fails for `n = 2`, `λ = (1)`
   (`EQZab.hat_d_printed_false`). Correct: `d(ŝ_λ) = Σ_{μ = λ + □_i} (−1)^{binom(n,2) + |i/λ|} {ct(□_i)} ŝ_μ`
   (`EQZab.hat_d_partition`; for every exponent vector, `EQZab.hat_d`), i.e. the printed sign `(−1)^{binom(n−1,2) + i − 1}`
   is replaced by `(−1)^{binom(n,2)}`.
19. **§4.3, linearity of the trace (4.24) [F→T].** For the right action `z · h = (θ ∘ w_0)(h) z` of Definition 4.6,
   `z^∨ = θ ∘ ∂_{a,b}` is not right `OΛ_{a+b}`-linear (`EQZab.trace_not_linear`, with `h = e_2`); it is `w_0`-semilinear,
   `z^∨(f z · h) = z^∨(f z) w_0(h)` (`EQZab.trace_mul_twistRev`), and `w_0 ∘ θ ∘ ∂_{a,b}` is linear (`EQZab.trace_linear`).
   Corollary 4.10 holds as printed for `z^∨ = θ ∘ ∂_{a,b}` (`EQZab.cor_4_10`) and hence also for `w_0 ∘ z^∨`, since
   `d ∘ w_0 = w_0 ∘ d`.
20. **§4.3, Lemma 4.4 [F→T].** The map `γ` of (4.10), `e_k ↦ (−1)^{binom(k,2)} e_k(x)`, is not an isomorphism of left
   `OΛ_a`-modules for the action of `OΛ_a` on `(OΛ_a ⊠ OΛ_b)/M` by `g(x)·`: for `(a, b) = (2, 2)` no additive map with the
   printed values is left `OΛ_2`-linear (`EQBorel.lemma_4_4_printed_false`; linearity would force `2 e_2(x) ∈ M`, while
   `e_2(x)` has infinite order modulo `M`). Correct: `γ(f) = w_0(f)(x) mod M` is well defined and bijective, with the printed
   values and `γ(h_k) = (−1)^k e_k(y)`, and it is `w_0`-semilinear, `γ(g f) = w_0(g)(x) γ(f)` (`EQBorel.lemma_4_4`,
   `gamma_elementary`, `gamma_complete`, `gamma_smul`; stated on EKL's `OH_{a,a+b}`, which `θ` identifies with the
   untwisted ring of the lemma). The printed proof works for this map: the two-sided ideal `⟨h_m : m > b⟩` equals the left
   ideal generated by the `h_m` (`EQBorel.leftIdeal_mul_mem`).
21. **§4.3, Prop 4.13 (3), the graded rank [F→T].** With the generator `1_z` of `Z_a` in degree `0` (as in Def 4.6 and its
   `r`-block analogue), `HOM_{OΛ_n}(Z_a, Z_b)` is free on matrix units of `q`-degree `2(|λ'| − |λ|)` and its graded rank is
   `q^{D_b − D_a} [n; a]_q [n; b]_q`, `D_a = Σ_k a_k (a_1 + ⋯ + a_{k−1})` (`EQBlocks.grankHom_eq`), not the printed
   `[n; a]_q [n; b]_q`; the two agree iff `D_a = D_b`, in either convention `q^{±deg}` (`EQBlocks.grankHom_eq_printed_iff`,
   `invert_grankHom_eq_printed_iff`), and differ for `a = (1, 1)`, `b = (2)` (`EQBlocks.prop_4_13_three_printed_false`).
   The printed formula is the graded rank after placing the generator of each `Z_a` in degree `−D_a`, the normalization
   under which `Z_a` itself has the symmetric graded rank `[n; a]_q` (as stated for `Z_{a,b}` before Cor 4.11).
22. **§4.4, footnote 5, the results over ℤ [G].** The footnote derives the statements of §4.4 over ℤ from formality and
   Theorem 2.7, but Corollary 2.6 needs a semisimple degree-0 part, which formality does not supply over ℤ. The statements
   hold over ℤ by a different route: `OΛ_n` and `OΛ_{a,b}` are connected over ℤ with `Z¹ = 0` and torsion-free `H²`
   (every cocycle in degree not divisible by 4 is a coboundary, `osym_eq_d_of_cocycle`, by Prop A.2 (2)), so their compact
   derived categories have `K₀ ≃ ℤ` (`baseK0OsymInt`, `baseK0OsymABInt`, from `DG.DGRing.K0.equivIntOfIsConnectedInt` in
   dg-lean), and Theorem 4.17 holds over ℤ (`thm_4_17_int_equiv`, `thm_4_17_int_mul`, `thm_4_17_int_comul`).
