# Append Mackey boundary: balance of P (proposed)

**Status: proposed written argument; not yet a Lean result.** It is the
Lean-setting form of `DeformedGlobalQP.md` §4 ("Old-generator P balance") for
the source side of `MackeyCosets` on the append side
(`DeformedMackeyBoundary.md` §1; Kang–Kashiwara–Oh, arXiv:1206.5933v2,
proof of Lemma 8.1, mirror form). It replaces the explicit expansion
`C S = Σ u p_u` of §4 by an induction on the length of the old word that
peels its last letter. No new idea is needed beyond the local relations
already in the library; the signs cancel (§3), so this bears neither on the
route nor on the truth of the conjecture.

Conventions as in Lean: the ground ring `k` is purely even, so the twist of a
homogeneous morphism `g` is `tw_q g = (-1)^(q|g|) g`; composition `f ≫ g` is
"`f` first"; a matrix entry `single row col f` has `f : col ⟶ row`. Fix the
moving colour `i` and cyclotomic polynomials `a` with
`CyclotomicPolynomialParity`; put `N = natDegree (a i)`.

## 1. The morphisms

For an old word `s` (a list) put

* `T_s = lastToFirstHom i s : s ++ [i] ⟶ i :: s`, the crossings moving the last
  strand to the front;
* `R_(i::s) = f_i(x₁)`, the polynomial `a i` in the first dot of `i :: s`
  (`aeval (dotE (i :: s) 0) (a i)`);
* `W_s = T_s ≫ R_(i::s) : s ++ [i] ⟶ i :: s` (algebra order `f_i(x₁) T`).

`W_s` is homogeneous of parity `q_s = p(i)(N + p(s))`: `T_s` has parity
`p(i)p(s)` and `f_i(x₁)` has parity `N p(i)` by homogeneity of `a i`.

Peeling the last letter (`lastToFirstHom_append_singleton`), with
`σ = cross |ν|` the crossing of the last two strands of `ν ++ [x] ++ [i]`,

    W_(ν++[x]) = σ ≫ (W_ν ▷ x),                                   (1)

because the first dot of `i :: ν ++ [x]` is the first dot of `i :: ν`
whiskered by `x`.

**The killed part.** For old words `s`, `u` let `Cyc(s, u) ⊆ Hom(s, u)` be the
span of `p ≫ R^(w) ≫ q`, where `R^(w)` is the first-dot polynomial
`f_(w₀)(x₁)` on a nonempty word `w`. It is a two-sided ideal of the old
category and is stable under right whiskering, `y ∈ Cyc ⇒ y ▷ x ∈ Cyc`,
since `R^(w) ▷ x = R^(w++[x])`. Put

    Kill(s, t) = span { (y ▷ i) ≫ h : y ∈ Cyc(s, u), h : u ++ [i] ⟶ i :: t }.

`Kill` is stable under postcomposition, under precomposition by `p ▷ i`
(`p` old), and under `K ↦ σ ≫ (K ▷ x)`: by super interchange,
`σ ≫ ((y ▷ i) ▷ x) = ± ((y ▷ x) ▷ i) ≫ σ'`, and `y ▷ x ∈ Cyc`.

**The error.** For an old morphism `g : s ⟶ t` (homogeneous) put

    E(g) = (g ▷ i) ≫ W_t − W_s ≫ (i ◁ tw_(q_s) g).

**Claim (P balance).** `E(g) ∈ Kill(s, t)` for every old `g`.

## 2. Proof

*Reduction to generators.* `E` is linear and, for `g₁ : s ⟶ u`,
`g₂ : u ⟶ t` with `p(s) = p(u)` (true along any chain of dots and
crossings),

    E(g₁ ≫ g₂) = (g₁ ▷ i) ≫ E(g₂) + E(g₁) ≫ (i ◁ tw g₂),

since `tw` is multiplicative for a fixed parity. Both terms lie in `Kill` by
the stabilities above. By `span_normalForms` every morphism is a linear
combination of composites of single dots and crossings, so it suffices to
treat one generator `g` on `s = ν ++ [x]`, by induction on `|s|`
(`|s| = 0` has no generator).

*(a) Inner generator,* `g = g' ▷ x`, `g'` a dot or crossing on `ν`. By (1),
super interchange of `g' ▷ [x, i]` with `σ`, and
`tw_(q_(νx))(g' ▷ x) = (-1)^(p(i)p(x)|g'|) tw_(q_ν)(g') ▷ x`
(`q_(νx) = q_ν + p(i)p(x)`), both terms of `E(g)` acquire the same sign
`(-1)^(|g'| p(x) p(i))`:

    E(g' ▷ x) = (-1)^(|g'| p(x) p(i)) σ ≫ (E(g') ▷ x).

By induction `E(g') ∈ Kill`, hence `E(g) ∈ Kill`.

*(b) Dot on the last old strand,* `g = ν ◁ x_dot`. By (1),
`(g ▷ i) ≫ W_(νx) = (dot ▷ i) ≫ σ ≫ (W_ν ▷ x)`. The dot slide (1.8) moves
the dot to the last strand with sign `(-1)^(p(x)p(i))` plus, only when
`x = i`, a signed identity term. Moving the last dot past `W_ν ▷ x` costs
`(-1)^(q_ν p(x))`. The total sign is `(-1)^(q_(νx) p(x))`, the sign of
`tw_(q_(νx)) g`, so the main terms cancel and

    E(g) = 0                       (x ≠ i),
    E(g) = ± W_ν ▷ i = ± (T_ν ≫ R_(i::ν)) ▷ i      (x = i).

In the second case `y = T_ν ≫ R_(i::ν) : ν ++ [i] ⟶ i :: ν` is an old
morphism in `Cyc`, so `E(g) = ±(y ▷ i) ≫ 𝟙 ∈ Kill`.

*(c) Crossing of the last two old strands,* `s = ν ++ [c, x]`,
`g = ν ◁ τ_(c,x)`. Applying (1) twice, both terms of `E(g)` are a braid word
in the window `(c, x, i)` followed by `W_ν ▷ [x, c]`:

    (g ▷ i) ≫ W = s₁ s₂ s₁ ≫ (W_ν ▷ [x, c]),
    W ≫ (i ◁ tw g) = ε s₂ s₁ s₂ ≫ (W_ν ▷ [x, c]),

with `ε` the product of the interchange sign `(-1)^(q_ν p(c) p(x))` and the
twist sign `(-1)^(q_(νcx) p(c) p(x))`. Since
`q_(νcx) − q_ν = p(i)(p(c) + p(x))` and `p(c)p(x)(p(c) + p(x)) = 0` in
`ZMod 2`, `ε = 1`. The braid relation (1.9) is sign-free (`braid_ne`), so
`E(g) = 0` unless `c = i ≠ x`. In that case (`braid_iji`) the difference is
the correction `C`, a polynomial in the dots at the window positions
`m−2, m−1, m` (`m = |s|`, position `m` the moving strand):

    E(g) = C ≫ (W_ν ▷ [x, i]).

Write each monomial as `(c_old ▷ i) ≫ (x_m)^d` with `c_old` an old dot
monomial on `ν ++ [i, x]`. The last dot supercommutes past `W_ν ▷ [x, i]`
(disjoint strands), and

    (c_old ▷ i) ≫ (W_ν ▷ [x, i]) = ((c_old ≫ (T_ν ▷ x) ≫ R^(i::ν++[x])) ▷ i),

an element `(y ▷ i)` with `y ∈ Cyc`. Hence `E(g) ∈ Kill`. ∎

## 3. Signs

Every sign is a product of interchange signs and twist signs; the twist
parity `q_s` changes exactly by `p(i)p(x)` per peeled letter, which is the
parity the moving strand meets when it crosses `x`. In (b) the dot slide
contributes the crossing parity, in (c) the change of `q` cancels against
the parity of the crossing of `c, x`. No sign fails; no division is used.

## 4. Matrix form and descent

Let `ψ = appendAlgebra i (n+1)`, `φ_L = prependAlgebra i (n+1) ∘ tw_ε`
with `ε = p(i)(N + p(β))`, `W = Σ_s single (i :: s) (s ++ [i]) W_s` over all
words of length `n+1`, and `J = Hn(n+2) · ψ(cyclotomicIdeal)` (a left ideal,
stable under right multiplication by `ψ(Hn(n+1))` since the cyclotomic ideal is
two-sided). For `g : t ⟶ s` with `t` of content `β`, the entry of
`W ψ(single s t g) − φ_L(single s t g) W` is `E(g)`, and
`Kill(t, s)` maps into `J` (`p ≫ R^(w) ≫ q` is the entry of
`single · q * gen w * single · p`). Hence, with `e_β` the content
idempotent,

    (W ψ(a) − φ_L(a) W) ψ(e_β) ∈ J        for all a ∈ Hn(n+1).       (2)

Let `B` be a left `Hn(n+1)`-module on which the cyclotomic ideal acts by zero
and `e_β` by the identity (the content corner `B_β`). Then (2) makes

    P : Ind_(φ_L) B → Ind_ψ B,    z ⊗ b ↦ z W ⊗ b

well defined: `z(Wψ(a) − φ_L(a)W) ⊗ b = z(Wψ(a) − φ_L(a)W)ψ(e_β) ⊗ b`, and an
element `c ψ(r)` of `J` gives `c ψ(1) ⊗ r b = 0`. This is the source module
`L₁ = e_R H e_L ⊗ Π^ε B` of `DeformedMackeyBoundary.md` §1: the Π^ε shift is
the twist `tw_ε` in `φ_L` (old balance `h φ_L(c) ⊗ b = h ⊗ φ^ε(c)` read through
`tw_ε² = 1`).
