# Input-side append coordinates and the left-oriented Mackey summand

## Status

- **Checked:** `QuiverHecke/AppendParabolic.lean` (unique factorization
  `w = u⁻¹ (v × 1)` in `S_m`, `m = n + 1`, with `u` a shuffle; length additivity;
  reduced crossing word `canWord m u⁻¹ ++ canWord n v`) and
  `QuiverHecke/AppendBasis.lean` (input leading-index equivalence
  `AppendIdx.leadEquiv`, the diagrams `appendElt`, their decomposition
  `appendElt_eq_comp`, unit leading terms `appendElt_approx`, and the scalar Hom
  basis `appendBasis` of `Hom(s ++ [i], t)`).
- **Proposed (not yet checked):** §§3–4 below.

This is the mirror of `PrependCoordinates.md`. It is needed for the left-oriented
crossing summand `ι(R) τ_n ι(R)` of `DeformedMackeyBoundary.md`, see the interface
note (ii) on `MackeyCosets` in `HANDOFF.md`: the right-oriented prepend coordinates
give the wrong polynomial component.

## 1. Permutations

Let `h : n + 1 = m`. A shuffle `u` for the blocks `n, 1` has `u⁻¹` increasing on
`0, …, n − 1`; it is determined by `j = u⁻¹(n)`, and `d_j = u⁻¹` moves the last
strand to position `j` keeping the order of the others. Every `w ∈ S_m` is
`d_j (v × 1)` for unique `v ∈ S_n`, `j`, and `ℓ(w) = ℓ(v) + ℓ(d_j)`
(`appendPermutation_bijective`, `length_appendPermutation`). Since the old block is
the first one, its reduced word needs no shift.

## 2. The scalar basis

For colours `s`, `t` and a colour `i`, the index `AppendIdx i s t` consists of a
new-strand exponent `m`, a sorted old dot list `L` on the first `|s|` strands,
`v ∈ S_|s|` and an append shuffle `u`, with the target condition. The diagram is,
chronologically: the old dots `L`, the old crossings `cw(canWord v)`, `m` dots on
the last strand, then the moving crossings `cw(canWord u⁻¹)`. Equivalently
(`appendElt_eq_comp`)

    appendElt(m, L, v, u) = c_u · x_last^m · (nf(L, v) ⊗ 1_i).

The last-strand dots commute with the old crossings exactly (the old crossings fix
position `|s|`, `extN_wordProd_inv_of_ge`), so after one braid normalization the
leading term is the normal form with dots `L ++ [|s|]^m` and permutation
`d_j (v × 1)`; there is no dot reordering, unlike the prepend case.
`basisOfTriangular` gives `appendBasis`.

## 3. Right-oriented affine coordinates (proposed)

With `B = Hn n`, `A = Hn (n+1)`, `ψ = appendAlgebra i n`, `e = ψ(1)`,
`C = {z ∈ A : z e = z}` and `x = affineLastDot i n`, the claim is the right
`B`-linear bijection

    Ψ : (Fin(n+1) × ℕ →₀ B) → C,   Ψ(b) = Σ_(j,m) c_j x^m ψ(b_(j,m)),

where `c_j` is the matrix of moving crossings `d_j`. The proof is that of
`prependCoordinateEquiv` with `appendBasis` in place of `prependBasis`: on each
matrix entry `(w ++ [i], t)` the terms `c_j x^m ψ(nf)` are the basis vectors
`appendElt`, the coefficient of `appendElt(m, L, v, u)` is the coefficient of
`nf(L, v)` in `b_(j,m)`, and entrywise assembly inverts `Ψ`. Balanced tensor
descent `C ⊗_B M ≅ (Fin(n+1) × ℕ →₀ M)` then follows as in
`PrependTensorCoordinates.lean`.

## 4. Left-oriented correction (proposed)

Write `c_n = 1` (no moving crossing) and, for `j < n`, `c_j = c'_j τ_n` with
`c'_j = τ_(j+1) ⋯ τ_(n−1)` (algebraic order) a crossing word on the first `n`
strands, so `c'_j ∈ ψ(B)`. The right-oriented crossing summand is
`⊕_(j<n,m) c'_j τ_n x^m ψ(B)` and the polynomial summand is `⊕_m x^m ψ(B)`.

On the last two strands, `τ_n x_(n+1) = ε x_n τ_n + δ`, where `ε = ±1` and
`δ ∈ {0, ±e}` (nonzero only for equal colours) are the existing dot-slide
coefficients. By induction on `m`,

    τ_n x_(n+1)^m = ε^m x_n^m τ_n + Σ_(a+b=m−1) p_(a,b) x_n^a x_(n+1)^b,     (1)

with scalars `p_(a,b)` (zero unless the last two colours agree). Since `x_n` and
the crossings of the first `n` strands lie in `ψ(B)` and `x_(n+1)` supercommutes
with `ψ(B)`, (1) gives for `b ∈ B`

    ψ(c'_j x_n^m) τ_n ψ(b) = ε^m c'_j τ_n x_(n+1)^m ψ(b) + Σ_l x_(n+1)^l ψ(N_(j,m,l) b)  (2)

with `N_(j,m,l) b` of `x_(n+1)`-degree `l < m`. Define the left-oriented summand

    F(u) = Σ_(j<n,m) ψ(c'_j x_n^m) τ_n ψ(u_(j,m)),     u : Fin n × ℕ →₀ B,

and `j(f) = Σ_l x^l ψ(f_l)`. By (2), `F = ε-signed right-oriented crossing part
+ j ∘ N` with `N` additive, so from §3:

- `F u + j f = 0` implies `u = 0` and `f = 0` (the crossing coordinates of the
  left side are `±u`, its polynomial coordinates are `N u + f`);
- every `y ∈ C` is `F u + j f`: take `u` from the crossing coordinates of `y`
  (with signs `ε^m`) and `f = (polynomial coordinates of y) − N u`.

These identities are right `B`-linear, so they descend through `− ⊗_B M`.

*Domain.* All of this takes place in the two-sided corner `e A e`, `e = ψ(1)`: the
crossing `τ_n` there is the equal-colour last crossing, so `ψ(c'_j x_n^m) τ_n ψ(u)`
depends only on `e' u` with `e' = ψ'(1)` (old words whose last colour is the appended
colour). The crossing coordinates are therefore `u : Fin n × ℕ →₀ e'B`, and the
right-oriented coordinates of an element of `e A e` with `j < n` lie in `ψ(e'B)`. The
matrix identity `c_j e = ψ(c'_j) τ_n` is `appendShuffleElement_castSucc_mul_corner`.

Moreover `F(Fin n × ℕ →₀ B) = ψ(B) τ_n ψ(B)`: by the append basis one level down,
`B = ⊕_(j<n,m) c'_j x_n^m ψ'(B')` as right `B'`-modules (`B' = Hn (n−1)`), and
`ψψ'(B')` commutes with `τ_n` up to sign, so `ψ(a) τ_n ψ(b)` is a sum of
`ψ(c'_j x_n^m) τ_n ψ(b' b)`. This is the left orientation needed for `P_short`.

The right-dot operator `R_t` is right multiplication by `x_(n+1)` (input side).
`R_t(j f) = j(t f)` is immediate. For the crossing summand, `x_(n+1)` passes
`ψ(u)` up to the sign of `u`, and `τ_n x_(n+1) = ε x_n τ_n + δ` gives

    R_t(F u) = F(X u) + j(single 0 (E u)),
    (X u)_(j,m+1) = ± ε u_(j,m),   E(u) = ± δ Σ_(j,m) c'_j x_n^m u_(j,m) ∈ B,

with the signs those of the supercommutation of `x_(n+1)` with `ψ(u)`. So `X`
is a signed shift of the exponent, with no lower correction. The exact signs are
fixed when `R_t` is constructed.
