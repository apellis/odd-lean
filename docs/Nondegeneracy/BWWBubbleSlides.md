# Bubble slides for Brundan–Wang–Webster parameters

This note covers the bubble slides and related distinct-colour identities of the Phase 1
proof, for Brundan–Wang–Webster parameters (arXiv:2505.22929v2, §2.2; see
`BWWParameters.md`). It lists the sites that use `p > 0` or `q > 0` for the monomials
`c i j p q u^p v^q` of `Qᵢⱼ(u, v)`, sorts them by what the pure terms (`p = 0` or `q = 0`,
including the constant term) change, and records the lemmas that handle them.

## 1. The box form of the bubble slide

Brundan–Ellis (arXiv:1701.04133v2) Proposition 7.3(iii), (7.11)–(7.12), slides a bubble of
colour `i` across a `j`-strand. The right-hand side is a sum over the monomials of `Qᵢⱼ`. For
a general coefficient function `c` on the box `p ≤ dᵢⱼ`, `q ≤ dⱼᵢ`, the sum has the form

    lbub(n) = Σ_{p ≤ dᵢⱼ, q ≤ dⱼᵢ} c(p, q) · x_j^q ≫ rbub(n + p - dᵢⱼ).

Its zero-dot row (`q = 0`) is

    tᵢⱼ · bub(n) + Σ_{r < dᵢⱼ} c(r, 0) · bub(n - (dᵢⱼ - r)).

With Brundan–Ellis parameters, `c(r, 0) = 0` for `r < dᵢⱼ`, and the row is the corner term.
In general the pure terms add lower bubbles with no dot on the `j`-strand.

The coefficient-level identities are in `OddMath/SKM/BWWBoxSums.lean`:

* `boxSum_eq_row_add`: the box sum is its row plus the part with `q > 0`.
* `boxSum_sub_row_mem`: modulo a submodule containing every `q > 0` term, the box sum is
  its row.
* `boxSum_sub_corner_sub_pure_mem`: modulo that submodule, the box sum is the corner term
  plus the pure terms.
* `boxSum_sub_corner_mem`: without pure terms, the box sum is the corner term.
* `boxSum_single_pure`: the corner term alone is wrong when a pure term is present.

## 2. Sites that use only the upper bound

At these sites the argument uses only `p < dᵢⱼ` or `q < dⱼᵢ` (plus parity or symmetry), and
pure terms satisfy these bounds too. After re-indexing `Ioo 0` to `range`, each becomes a box
sum. The statements change; the proofs go through term by term.

| Module | Declarations | Use |
|---|---|---|
| `SKM/BubbleSlidesConnected` | `bubbleR_conv_normalize`, `bubbleL_conv_normalize`, `eq_7_11_connected`, `eq_7_12_connected`, `bubbleSlideRHSR`, `bubbleSlideRHSL` | bound `p < dᵢⱼ`; parity of `dᵢⱼ - p` |
| `SKM/BubbleSlideInduction` | slide induction step | bound only |
| `SKM/BubbleSlideConvolution` | `bubbleSlideRawConv_split` | uniform in `p` |
| `SKM/BubbleSlideMiddle`, `SKM/BubbleSlideDotted` | term lemmas | arbitrary `q` |
| `SKM/OddBubbleCentrality` | `bubRs_one_slide_ne` | parity and bound; the odd bubble still slides unchanged |
| `SKM/Lemma71`, `SKM/Lemma71Cup` | Lemma 7.1 cap and cup sums | bound only |
| `SKM/Lemma32`, `SKM/Lemma33`, `SKM/Lemma33Rot` | quadratic relation consequences | parity and `c_symm` |
| `SKM/RouquierDistinctCapColumns` | `distinctCapColumn_monomial_zero` | any `p`, `q` |
| `SKM/RouquierDistinctCupRows`, `RouquierDistinctCupTests`, `RouquierDistinctCapPrincipal`, `RouquierDistinctConnectedCapBoundary` | distinct-colour cap and cup expansions | bound only |
| `SKM/RouquierDistinctCapMiddle` | middle cap terms | `0 < p`, but the `p = 0` terms have an empty range in `braidSum` |
| `QuiverHecke/CyclotomicAction/ELVAppendQPLeading`, `ELVBoundaryNumeratorLeading`, `ELVQPRegularity`, `ELVAppendNormRegularity`, `EndpointNormPolynomial` | leading-term and regularity estimates | `e < dᵢⱼ`, arbitrary in the other exponent |

## 3. The site that uses the lower bound

`SKM/PositiveDotTransport.bubLs_slide_difference` uses `0 < q` (through
`dots_rbub_bubLs_mem_positive`) to show that sliding a bubble across a strand changes it only
by terms with a positive number of dots. The zero-dot term it records is `tᵢⱼ · γ`. With pure
terms, the zero-dot term is the whole row of §1: `tᵢⱼ · γ` plus lower bubbles. This result
feeds the upward-to-oriented reduction of Brundan–Ellis §8:

* `normalized_bubLs_slide_difference`, `betaSYMGen_slide_difference`;
* `UpwardWordTransport`: `betaSYM_upward_word_difference`,
  `betaSYM_exists_positiveWordExpansion`;
* `ClosureCoefficientExpansion`: `rightClosure_betaSYM_expansion`,
  `rightClosure_partialMate_betaSYM_expansion`;
* `WeakMateIndependence`: `closure_decorated_coefficient`, `strict_injective_of_top_data`;
* `TopClosureCoefficients`.

**Effect.** The principal coefficient of a closure becomes `φ(p)`, not `p`, where `φ` is the
identity plus a map that strictly lowers bubble degree. (Each pure term replaces a bubble by
one of strictly smaller degree.) Such a map is bijective on the symmetric-function
coefficients, which are exhaustively filtered by degree. So the injectivity argument survives
once the detector allows a twisted principal coefficient. This is a change of route, not of
the statement.

`OddMath/SKM/TwistedClosureDetector.lean` gives the two abstract facts:

* `injective_of_positive_closure_twisted`: `injective_of_positive_closure` with principal
  coefficient `φ p` for an injective additive `φ`;
* `bijective_id_add_of_lowering`: `id + N` is bijective when `N` lowers an exhaustive
  filtration.

## 4. Remaining steps

1. Restate the slide term lemmas against `presBWW` (`QuiverHecke.presBWW`; `SKM.presBWW`
   once it is available), in new files, using the box sums of §1.
2. State the version of `bubLs_slide_difference` with the row of §1 as zero-dot term. Show
   that the row is the image of `γ` under a map of the form `tᵢⱼ · (id + N)`, with `N`
   lowering bubble degree.
3. Thread the twisted detector through the §8 chain of §3.

The sites in `MixedEntry`, `MixedEntrySourceUnits` and `ProbeMixedRelations`, where an
invertible leading coefficient is used, are treated separately.
