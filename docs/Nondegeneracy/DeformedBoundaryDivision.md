# Deformed boundary norm and polynomial division

**Status: proposed written proof, pending independent criticism; not a Lean
result.** The boundary construction and compatible lifts in
`DeformedMackeyBoundary.md` remain a pending input. This note supplies the
norm comparison and division calculation for those specified maps, rather
than assuming their leading-degree conclusion. It uses the full-coefficient
QP identity of `DeformedGlobalQP.md`, with the local sign correction in §2.

Sources compared: KKO I, arXiv:1206.5933v2, (8.4)–(8.5), Corollary 8.6,
diagram (9.5), Proposition 9.3, Lemma 9.5 and Theorem 9.6. The extension to
odd deformation coefficients is the argument below, not a claim of that paper.

## 1. Coordinates and the two different products

Retain the finite compatible ELV support and coefficient relations of
`DeformedSquareResolution.md`. Thus no exterior-flatness is assumed. Write
R=A⊗ˢR(β), B=R/I, H=A⊗ˢR(β+α_i), n=|β|, and use the old-left and
old-right embeddings ι_L,ι_R and ideals J_L,J_R. Put p=p(i),
η=p p(β), r=p N_i, ε=η+r, m=the multiplicity of i in β.
All parity automorphisms φ act on coefficients as well as diagrams.
Let T=τ₁⋯τ_n, U=τ_n⋯τ₁, G=g_n⋯g₁, G'=g₁⋯g_n.
Products include their compatible endpoint idempotents.

For an old word ν define, in the last-dot skew polynomial algebra,

    S_ν(t)=∏_(ν_b=i)(t^(1+p)−x_b^(1+p))²,
    L_ν(t)=∏_(ν_b≠i)Q_(i,ν_b)(t,x_b)
                 ·∏_(ν_b=i, p=1)(t²+x_b²).

Write S=Σ_ν S_ν e(ν), L=Σ_ν L_ν e(ν). The factors of L are even
and commute with t. This does NOT make f_i(t)L commute with t.
In particular the repeated-odd factor of L is t²+x_b², whereas that
of S is (t²−x_b²)². Neither is replaced by the other below.

For odd i, the pending boundary has

    ρ(h⊗π^ε b)=(-1)^η h(x₁+2(-1)^r d_i)⊗π^ε φ(b),
    ρ̄(v_l b)=v_(l+1)φ(b)+2v_l d_i φ(b),
    w_(2q)=v_(2q),    w_(2q+1)=v_(2q+1)+2v_(2q)d_i.

Hence ρ̄(w_k b)=w_(k+1)φ(b), and ρ̄² is the square-dot action.
At even i, take ρ(h⊗b)=h x₁⊗b, w_k=v_k and φ^p=1.
The target last-dot action is R_t(h⊗b)=h x_(n+1)⊗φ^p(b).
The pending construction proves Pρ=R_tP, B₁ρ=ρ̄B₁, C₀P=A_∂B₁,
and supplies compatible lifts ℓ(w_k)=z_k. Its extraction convention is

    B₁(x_(n+1)^l a U⊗π^ε b)=v_l φ^r(a)b.

The twist φ^r will be harmless on S's even coefficients, but cannot
be omitted on a general coefficient.

## 2. Local normalization and injectivity of G

Use precisely KKO's g, not its negative. With x=x_a, y=x_(a+1),
D=y²−x² and E=y−x on an odd equal-colour corner, the local relations give

    τD=−Dτ+2E,   τE=Eτ,   E²=x²+y²,
    g=D(E−Dτ)=(E−τD)D,    τg=τDE,
    g²=−D²(x²+y²).                                      (1)

Indeed Φ=E−Dτ satisfies Φ²=x²+y² and ΦD=−DΦ, proving the last
identity. At even equal colour put D=y−x; then

    τD=−Dτ+2,    g=D(1−Dτ)=(1−τD)D,
    τg=τD,       g²=−D².                               (2)

For distinct colours g=τ and its square is the prescribed Q factor.
These identities use no cyclotomic polynomial.

There is a sign error in the displayed local rewritings in
`DeformedGlobalQP.md` §3: `(τD−E)D` and `(τD−1)D` must respectively
be `(E−τD)D` and `(1−τD)D`. Its displayed formulas for τg already
have the correct source sign. Its subsequent cancellation equation is
unchanged: setting f_i T_(n−1)g_n V=0 yields
`Z D₀=(-1)^h A_(ν<)E₀D₀` with either corrected rewriting above.
Thus its surviving positive factor x₁²+x_(n+1)² and its final QP
formula are unchanged. This is a correction to that note, not to KKO.

We need injectivity of right multiplication by G on H e_R/J_R, not
just injectivity of QP. It follows directly from (1)–(2). The reverse
chain G' transports every old generator back, with the same total-parity
twist, and transports each homogeneous old f_j to its corresponding
old position. Consequently J_L G'⊆J_R and J_R G⊆J_L. These are
statements about the explicit left-ideal quotients; they do not require
an identification of their different twisted right actions.

Expand GG' by cancelling its innermost pair of g's successively.
Intertwiner dot transport carries each resulting square to the endpoint
coordinates. The result is a polynomial K_ν(x_(n+1)) on each word,
with one Q factor per distinct colour, one factor
`−(x_(n+1)−x_b)²` per repeated even colour, and one factor
`−(x_(n+1)²−x_b²)²(x_(n+1)²+x_b²)` per repeated odd colour.
All transported factors are even; the odd-variable powers in Q are even.
In particular there is no extra transport sign in these factors.
Each K_ν has a unit leading coefficient, the product of the assumed
Q leading units and the displayed minus signs. Its moving degree and
leading unit depend only on content.

In the right-oriented affine PBW decomposition, tensor with B and place
the moving last dot before the old coefficient. Multiplication by K
has scalar unit leading term on every coset coordinate and lower moving
powers otherwise. The largest moving exponent of a finite nonzero vector
cannot disappear. Thus right multiplication by K=GG' is injective on
H e_R/J_R. If hG=0 modulo J_L, then hGG'=0 modulo J_R, so h=0.
This proves the required injectivity of G without inverting any polynomial,
using freeness of B over A, or asserting that QP injective implies Q injective.

## 3. Reverse norm comparison with all coefficients

Write L_left for L with moving variable x₁ and old variables x_(b+1).
The corrected all-prefix identity is

    f_i(x₁) T G = f_i(x₁)L_left       modulo J_L.       (3)

For each homogeneous monomial c x₁^l of f_i, its parity is r.
Transport through G contributes (-1)^(η|c|) from c and (-1)^(ηl)
from the dot, whose product is (-1)^(ηr). Thus, exactly,

    G f_i(x₁)=(-1)^(ηr) f_i(x_(n+1))G,
    G L_left=L G.                                     (4)

Multiplying (3) on the left by G and applying (4) shows

    (G f_i(x₁)T−(-1)^(ηr)f_i(x_(n+1))L)G=0 mod J_L.

The injectivity proved in §2, applied to the parenthesized element of
H e_R/J_R, proves the reverse norm identity

    G f_i(x₁)T=(-1)^(ηr)f_i(x_(n+1))L mod J_R.         (5)

This is the coefficient-sensitive replacement for the norm input to
KKO Proposition 9.3. It keeps f_i on the left of L and never moves f_i
through a bare crossing. In particular (5) is not obtained by an
unverified ordinary anti-involution on the coefficient superalgebra.

## 4. Longest extraction and every corrected iterate

In expanding G, only the term taking the crossing part of every g_a
has permutation U. Any omitted crossing has smaller Coxeter length.
The equal-colour crossing coefficient is minus the square difference
in S; distinct colours contribute 1. Transporting their even polynomial
coefficients gives

    B₁(G e_L⊗π^ε1)=(-1)^m S(ρ̄)w₀.                  (6)

Here S(ρ̄)w_k means explicitly Σ_j w_(k+j)b_j when S=Σ_j t^j b_j.
For odd i only even j occur and each b_j is even. Formula (6) includes
φ^r(b_j)=b_j; no coefficient involution has been discarded. The result
uses w_even=v_even, so there is no extra d_i term at this base step.

Apply ρ^k to the lift G⊗π^ε1. Since B₁ intertwines ρ and ρ̄,
its extraction is (-1)^m S(ρ̄)w_k. On the other hand (5) says its
P-image at k=0 is entirely in the polynomial summand. That summand
is preserved by R_t, and Pρ=R_tP. Therefore for every k≥0,

    A_∂(S(ρ̄)w_k)=(-1)^(ηr+m) f_i(t)L(t) t^k.         (7)

In particular (7) at k=0 is the requested base value. The t^k is on
the RIGHT: replacing this expression by t^k f_i(t)L(t) would generally
be false for deformed odd f_i. For odd k, the source is the corrected
w_k, including +2v_(k−1)d_i at either cutoff parity.

The first-order defect is compatible exactly, not just in highest degree.
For the lifts ρ^k(G⊗π^ε1), the crossing component of P is zero by (5).
Their defect is therefore zero. For the compatible section ℓ, another lift
with the same B₁ value differs by an element of ker B₁. Its P-image has
zero polynomial projection; applying ρ still has zero polynomial
projection, because ker B₁ is preserved. Hence both choices give the same
boundary defect, and

    A_∂(S(ρ̄)w_(k+1))−A_∂(S(ρ̄)w_k)t=0.

Equivalently the pending identity Eψ(v)=A_∂(ρ̄v)−A_∂(v)t gives
Eψ(S(ρ̄)w_k)=0. No equality of the two crossing components themselves
is required.

## 5. Finite monic division

Put φ_k=A_∂(w_k), D=deg_t S=2(1+p)m and a=⟨h_i,Λ−β⟩.
The compatible-lift identity gives

    φ_(k+1)−φ_k t=Eψ_k ∈ B.                          (8)

For every j≥0, telescoping (8) shows

    deg_t(φ_(k+j)−φ_k t^j)<j.                        (9)

For j=0 the difference is zero. This is a direct finite induction and
uses no commutativity of B. Write S=Σ_(j=0)^D t^j b_j with b_D=1.
For odd i all b_j are even and only even j occur. For even i the
moving variable commutes with B. Right B-linearity and (9) imply

    deg_t(A_∂(S(ρ̄)w_k)−φ_k S)<D.                   (10)

If D=0 this difference is zero. Notice that this proof does not use
the source's claim that its numerator commutes with t; that claim
cannot simply be extended to odd deformation coefficients.

Let q be the leading coefficient of L in t. It is the product of the
prescribed leading units of Q_(i,j), counted with their multiplicities
in β; repeated odd factors have leading coefficient 1. Thus q is one
central even unit independent of the word ν. Define

    γ=(-1)^(ηr+m)q^(-1),      F=q^(-1) f_i(t)L(t).

F is monic of degree a+D. Combining (7) and (10) gives, for every k,

    F t^k = γφ_k S + h_k,          deg_t h_k<D.       (11)

This is the ordered right-division identity. It proves

    φ_k=0                              if a+k<0,
    γφ_k=t^(a+k)+lower moving powers    if a+k≥0.    (12)

Indeed a nonzero polynomial times the monic S has degree its degree
plus D, even when B has zero divisors. If a+k<0, the left side of
(11) has degree below D, forcing the quotient to vanish. Otherwise
its top coefficient is 1 and forces the top coefficient of γφ_k to
be 1 at degree a+k. The argument also applies componentwise on zero
corners; on the zero ring the displayed polynomial identities retain
their literal meaning. No inverse coefficient beyond q is used.

Everything is finite: each word expansion, each PBW vector and each
polynomial in (9)–(11) has finite support. No numerical inversion,
degree sweep, fraction field or flatness over the exterior subalgebra
enters this proof.

## 6. Scope of the conclusion

Equations (7), (11) and (12) supply the proposed division step in the
corrected w-basis, subject to review of the pending boundary construction
and of this proof. They do not identify the prescribed categorical matrix.
The source matrices `[F̄,j(1),…,j(t^(a−1))]` for a≥0 and
`[F̄;E;EX;…;EX^(−a−1)]` for a<0 still require comparison with the
fixed tensor-unit/counit mate and the prescribed signed dot/crossing maps
of `DeformedRouquierMatrix.md`. In particular the cap rows EX^r are
not identified here with the required categorical dotted caps. No full
action, opposite-side projectivity, reverse adjunction or Lean theorem
is asserted.
