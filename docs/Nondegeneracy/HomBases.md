# Hom bases, `β_λ` and graded dimensions

Consequences of the Nondegeneracy Conjecture of Brundan–Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, §8, as proved by
`QuiverHecke.nondegeneracy_of_symmetrizer` for a Cartan superdatum with a symmetrizer,
homogeneous parameters (1.31) and a commutative ground ring `k` with `2` invertible.
Lean: [HomBases](../../OddMath/QuiverHecke/HomBases.lean); consumer:
[HomBases](../../scripts/NonVacuity/HomBases.lean).

## The coefficient algebra

`SYM` is the abstract algebra of (1.21)–(1.22) (`OddMath/SKM/BubbleAlgebra.lean`): for each
colour `i`, polynomial generators `e_{i,r}` (`r ≥ 1`), and for each odd colour one more
generator `δ_i` with `δ_i² = 0`; generators of different colours supercommute.
`SYM.coefficientBasis` is its monomial basis over `k`, indexed by pairs of a finitely supported
exponent function on `I × ℕ` and a finite set of odd colours (an exterior monomial in the
`δ_i`). In particular `SYM` is free over every `k`.

## `β_λ` is an isomorphism

The case `a = b = ∅` of the conjecture is injectivity of `β_λ : SYM → End(1_λ)`
(`betaSYM_injective_of_nondegeneracy`). Surjectivity holds without the conjecture: Theorem 8.1
with empty boundary uses the single matching with no strands, whose diagram is the identity,
so every endomorphism of `1_λ` is `β_λ(p)` (`endOne_mem_bubbleSpan`). Hence
`betaSYMEquiv : SYM ≃ₐ End(1_λ)`.

## Hom spaces are free

Fix `a, b` with `wt(a) = wt(b)`, a weight `λ`, and a complete set of pairwise inequivalent
strictly reduced `ab`-matchings with distinguished points (`MatchingBasisChoice`). The
labels are the decorated matchings `σ` (a matching with a dot count on each strand). The
expansion

  `(p_σ)_σ ↦ Σ_σ f(σ, λ) β_λ(p_σ)`

is a `k`-linear bijection from finitely supported families in `SYM` onto
`Hom(E_a 1_λ, E_b 1_λ)` (`expansionEquiv`), and it is right `SYM`-linear
(`expansion_mapRange_mul`), so this is the statement that the Hom space is a free right
`SYM`-module on the `f(σ, λ)`. Combining with the monomial basis of `SYM` gives a basis over
`k`:

  `{ f(σ, λ) β_λ(m) : σ decorated matching, m a monomial of SYM }`

(`homBasisOfSymmetrizer`, `homBasisOfSymmetrizer_apply`); in particular the Hom space is a
free `k`-module (`free_hom`). The degree and parity of `f(σ, λ) β_λ(m)` are the sums of those
of `σ` and `m`, and the expansion restricts to each component of fixed degree and parity
(`componentEquiv`).

## Graded dimensions

Assume now that `k` is a field with `2 ≠ 0` and that only finitely many colour-degree
generators of `SYM` occur in each degree (`DegreeLocallyFinite`, automatic for finitely many
colours). Then every component is finite-dimensional and

  `dim Hom(E_a 1_λ, E_b 1_λ)_{n,p} = Σ_σ dim SYM_{(n,p) − deg σ}`,

a finite sum over the decorated matchings of degree at most `n`
(`wordHomComponent_finrank_eq_sum`). With `π ↦ s`, `s² = 1`, the graded superdimension
`dim_{q,π} Hom` has coefficient of `qⁿ` equal to `Σ_σ s^{par σ} S_{n − deg σ}`, where
`S = dim_{q,π} SYM` (`homDimension_coeff_eq_sum`). For a root datum of the covering quantum
group, BE2's Theorem 12.1, equation (dum), follows:

  `dim_{q,π} Hom(E_a 1_λ, E_b 1_λ) = ⟨e_a 1_λ, e_b 1_λ⟩ · S`

(`homDimension_eq_form_mul_symDimension`), now without the conjecture as a premise. Here `S`
is the actual graded superdimension of `SYM`; the product printed in the proof of
Theorem 12.1 needs the odd-colour correction of ERRATA [BE2] 8,
`S = ∏_{i even} ∏_{r≥1} (1 − q_i^{2r})⁻¹ · ∏_{i odd} (1 + π q_i²) ∏_{r≥1} (1 − q_i^{4r})⁻¹`.

The coefficients of `S` count monomials of `SYM` (`SYM.componentBasis`,
`SYM.finrank_component`, `symDimension_coeff_eq_card`). Expanding the product monomial by
monomial gives the product identity as formal power series in `q`, with `π ↦ s`:
`SKM.hasProd_symFactor` states that the factors `SKM.symFactor` (`(1 − q^{deg e_{i,r}})⁻¹` for
the even generators `e_{i,r}`, `1 + s q^{2 d_i}` for the odd generators `δ_i`) have product
`S` in `PowerSeries ℚ` with the coefficientwise topology, and `SKM.symDimension_eq_tprod`
reads it in Laurent series. The generic step is `MonomialSeries.hasProd_monomialSeries`.
Composed with (dum):

  `dim_{q,π} Hom(E_a 1_λ, E_b 1_λ) = ⟨e_a 1_λ, e_b 1_λ⟩ · ∏_g symFactor g`

(`homDimension_eq_form_mul_tprod_symFactor`).

## Open

* `DegreeLocallyFinite` is an intermediate hypothesis of the dimension statements; it holds
  for finitely many colours. The infinite-colour reading is ERRATA [BE2] 15.
* Inhomogeneous parameters (Phase 2) are not covered.
