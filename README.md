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
