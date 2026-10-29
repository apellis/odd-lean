# Right projectivity from the deformed square resolution

**Status: written right-projectivity argument; not a Lean theorem.**
This assembles right projectivity from the all-prefix identity and P balance
in `DeformedGlobalQP.md` and the written ideal equality
in `DeformedIdealSum.md`. Full ELV P/Q descent, the signed QP identity and
injectivity of P are now proved in Lean. `ELVContentModule.lean` constructs
the content-level ordinary right B[s]-modules and the injective B[s]-linear P.
The finite-projective PBW decomposition and ideal-sum exactness below remain
written mathematics.
No assertion about left projectivity or the specified Rouquier matrix is made.

Sources read for this comparison: KKO I, arXiv:1206.5933v2, Lemma 7.3,
(8.1)–(8.5), Lemmas 8.1–8.2, Proposition 8.4 and Theorem 8.5;
ELV, arXiv:2203.14153v2, (3.24)–(3.27), (4.15)–(4.16);
Kang–Kashiwara, arXiv:1102.4677v4, Lemma 4.18 and its proof (pp. 27–28).
The extension of the coefficient ring below is not a theorem attributed to KKO.

## 1. Objects and ordinary right actions

Use exactly the coefficient algebra A and finite compatible support of
`DeformedIdealSum.md` §1: the purely even base has 2 invertible, leading
KKO coefficients are units, and every positive even odd-colour cutoff has
the relation d_j χ_(j,top)=0. Set R=A⊗ˢR(β), B=R/I,
H=A⊗ˢR(β+α_i), e_R=e(β,i), e_L=e(i,β), |β|=n.
The inclusions ι_R and ι_L have these corner units. Write
p=p(i), η=p p(β), r=p N_i, ε=r+η (parities modulo two), and let φ
be parity on the ENTIRE algebra, including A. Then

    K₀=H e_R⊗_R B,
    K₁=H e_L⊗_R Π^ε B,
    K₁′=H e_L⊗_R Π^η B.

For a shift a, the balance is
hι_L(c)⊗π^a b=h⊗π^a φ^a(c)b; the right action is
(h⊗π^a b)c=h⊗π^a(bc). In particular, forgetting parity does not
remove the left φ^a twist. In quotient coordinates the identification is

    h⊗π^a b ↦ [hι_L(φ^a(b))].

Thus the underlying quotient is H e_L/J_L, but its right action in these
coordinates is [h]·b=[hι_L(φ^a(b))], not the untwisted action.
The vanishing submodule J_L=Hι_L(I) is unchanged because φ(I)=I.
The K₀ quotient is H e_R/J_R, J_R=Hι_R(I).

The ordinary central variable needed below acts by

    (h⊗b)s = h x_(n+1)^(1+p)⊗b,
    (h⊗π^a b)s = h x_1^(1+p)⊗π^a b.                 (S)

At p=0 use s=t; at p=1 use s=t². The indicated dot (or square)
commutes with the whole corresponding old algebra: for p=1 two
supercommutation signs cancel, including signs from odd coefficients.
Consequently (S) respects tensor balance, preserves J_R or J_L, and
commutes with the unchanged right B action. This constructs ordinary
right B[s]-modules, where B means its underlying associative ring;
B need not be commutative. No super-opposite ring is involved.

For comparison only, the usual unsquared actions are

    (h⊗b)t = h x_(n+1)⊗φ^p(b),
    (h⊗π^a b)t = (−1)^η h x_1⊗π^a φ^p(b).

They supercommute with B, rather than commute when p=1. Their squares
are precisely (S). One must NOT claim that P intertwines these t-actions.
The normalizer of f_i is x↦x−2d_i, together with total coefficient
parity φ^r; its inverse sends x to x+2(−1)^r d_i. Both fix x² because
x d_i=−d_i x and d_i²=0. At zero cutoff put d_i=0. This explains why
restriction to (S), rather than unchanged t-linearity, is legitimate.

## 2. Affine PBW projectives, before and after quotient

Here is a direct construction of the projective structures, not a dimension
comparison. For each endpoint choose the subgroup S_n fixing that endpoint,
and minimal representatives D for S_(n+1)/S_n. Choose the reduced word for
wv with w∈D and v∈S_n to be the concatenation of the chosen words.
Let z be the endpoint dot and e_end(ν) the word idempotent (ν,i) or (i,ν).
Right-oriented affine PBW gives the right R-module isomorphism

    ⊕_(w∈D, ν∈I^β, k≥0) e(ν)R
      → H e_end,
    b in the (w,ν,k)-summand ↦ τ_w z^k ι_end(b).       (PBW)

The idempotent on b inserts e_end(ν) before its old algebra factor.
A basis of e(ν)R expands the old dots and old permutations; length
additivity gives exactly the selected full PBW permutations, and ordering
z ahead of the old dots costs only unit signs. This proves independence
as well as spanning. Equivalently one may obtain right-oriented PBW by
triangular dot slides from the usual PBW theorem. No cyclotomic relation
has been used and no flatness has been presumed. Tensor extension from
the scalar affine PBW theorem is extension of an explicit isomorphism.

Tensor (PBW) with B for K₀ and with Π^a B for the first-position modules.
The elementary map e(ν)R⊗_R Π^a B→π^a e(ν)B sends
c⊗π^a b to π^a φ^a(c)b. Its inverse sends π^a b to e(ν)⊗π^a b.
It is right B-linear and uses φ(e(ν))=e(ν). Thus it preserves corners,
including corners that become zero in B. It is not an appeal to exactness
of tensoring an arbitrary sequence.

Since z^(1+p) commutes with the old algebra, (S) raises k by 1+p
without mixing w or ν. Splitting k=(1+p)q+δ, 0≤δ≤p, now gives

    K₀ ≅ ⊕_(w,ν,δ) e(ν)B[s],
    K₁ ≅ ⊕_(w,ν,δ) e(ν)B[s],                       (Pj)

as ordinary right modules, with the appropriate degree and parity shifts
on each summand if these gradings are retained. For K₁ the displayed
isomorphism sends b s^q to τ_w z^(δ+(1+p)q)⊗π^ε b;
the inverse is the twisted coefficient map just given. In raw quotient
coordinates its coefficients are φ^ε(b). Each e(ν)B[s] is a direct
summand of B[s]. There are finitely many indices w,ν,δ. Hence both
modules are finite projective over B[s], regardless of A-flatness of B.
The same construction applies to K₁′. This is the required projective
structure on the actual tensor quotients, not on replacement modules.

## 3. P-linearity and injectivity with the typed Q target

**Checked injectivity.** `ELVPInjective.lean` proves `ELVOld.pMap_injective`
for arbitrary words, cutoffs and full exterior coefficients. The actual
quotient composite `qMap_comp_pMap` is `signedQPMap`; its injectivity follows
from `projection_qp_relation_regular` and the proved moving PBW coordinates.
`ELVOld.pPolynomial_injective` now transports this injectivity to
the content-level ordinary right B[s]-linear map. The exact projective
sequence, including the finite-projective PBW identification, remains open.

Put T=τ₁⋯τ_n and W=f_i(x₁)T e_R. The old balance in
`DeformedGlobalQP.md` defines the even map

    P(h⊗π^ε b)=hW⊗b.

Its right B-linearity is immediate from the last factor. Sliding the
moving last dot through T gives

    W x_(n+1) ≡ (−1)^η f_i(x₁)x₁T  (mod J_R).       (D)

Each deletion error is f_i times T with one crossing omitted. Moving its
disjoint crossing tail to the left puts its remaining right factor in the
old algebra, exactly as in the old-dot balance calculation. Thus the error
lies in J_R. To iterate (D), its error may be multiplied on the right by
the moving dot because that dot supercommutes with the old algebra and
J_R is homogeneous. It follows that

    W x_(n+1)² ≡ f_i(x₁)x₁²T = x₁²W.

At even i, (D) already reads W x_(n+1)=x₁W. Therefore P is B[s]-linear.
This proof uses the fixed square of the normalizer, not centrality of f_i.
The quotient projection K₀→F=(H/HF₁H)e_R is also B[s]-linear.

Use Q:K₀→K₁′, not a map to K₁ when r=1, with formula
Q(h⊗b)=h(g_n⋯g_1)⊗π^η b. Total-parity intertwiner balance and
transport of the old relation give its descent. The all-prefix formula is

    QP(h⊗π^ε b)=h f_i(x₁) L_ν(x₁)⊗π^η b,
    L_ν=∏_(ν_a≠i) Q_(i,ν_a)(x₁,x_(a+1))
          ∏_(ν_a=i odd)(x₁²+x_(a+1)²)

on the right word (i,ν). The second product is absent for even i.
This is a map between the two twisted quotients, not an unshifted
endomorphism. In raw quotient (PBW) coordinates its highest moving-dot term sends a
coefficient b to a unit times φ^r(b), possibly with a parity sign from
normal ordering. It stays in the same w,ν coordinate. Indeed the leading
coefficient of f_i is 1, those of each Q in the moving variable are units,
and each repeated-odd factor has leading coefficient 1. The degree is
independent of ν at fixed content; alternatively one can argue separately
in each right-word component. Lower terms have strictly smaller moving
degree. The largest moving exponent in a finite nonzero coordinate vector
therefore cannot disappear. This proves QP injective and hence P injective;
no faithfulness of a cyclotomic representation is used.

Equivalently, in explicitly right-B-linear tensor coordinates put
E^a_(w,ν,k)(b)=τ_w z^k⊗π^a b. If D is the leading moving degree and
u its scalar unit, the same calculation reads

    QP(E^ε_(w,ν,k)(b)) = E^η_(w,ν,k+D)(u b) + lower moving-degree terms.

The apparent coefficient semilinearity in raw quotient coordinates disappears
in these tensor coordinates because ε+r=η. It is not an extra twisting of
the ordinary right-B-linear map.

Using equality (IS2) in `DeformedIdealSum.md`, its kernel
calculation identifies im P with ker(K₀→F). We obtain the actual sequence

    0 → K₁ → K₀ → F → 0                              (E)

of ordinary right B[s]-modules with the projectives (Pj). The equality
(IS2), not a comparison of ranks, supplies its cokernel assertion.

## 4. A central monic annihilator without faithfulness

There is a short way to supply the global annihilator without extending
KKO's annihilator propagation directly to odd coefficient scalars.
Let J⊂A be generated by the finitely many odd parameters on the compatible
support, and let ℓ be their number. Then J^(ℓ+1)=0, and JH is a two-sided
ideal since coefficients supercommute with homogeneous affine elements.
The same nilpotence holds for its image in C=H/HF₁H.

The quotient C/JC is the KKO cyclotomic algebra over A/J, literally from
the generators and relations: f_j reduces to C_j(x²), x C_j(x²), or the
even-colour polynomial as appropriate. This needs no flatness. KKO
Lemma 7.3, applied over the purely even parameter ring A/J, supplies a
monic polynomial killing the last dot in this quotient. Its proof supplies
a polynomial in the last square as well. In particular choose a monic
g(s) annihilating the moving s-coordinate: for even i a square polynomial
also gives a monic polynomial in s=x_(n+1), and for odd i use s=x_(n+1)².
Only the finitely many words of content β+α_i occur, so products used to
uniformize the polynomial are finite. Zero cutoffs cause no exception.

Lift its coefficients to the even polynomial parameter subring of A,
which maps onto A/J. These lifts are central in H and in B, although
A as an ordinary ring need not be commutative. Denote the lifted monic
polynomial by g̃. The element g̃(s)e_R lies in JC. Therefore

    a(s)=g̃(s)^(ℓ+1) ∈ Z(B)[s],       F a(s)=0.        (A)

To see the last equality literally, compute in the corner e_R C e_R:
g̃(x_(n+1)^(1+p))e_R lies in the nilpotent ideal, so its (ℓ+1)-st power
is zero; right multiplication by it is exactly the action on F. Its
coefficients come from A, not an asserted faithful image of A inside C.
A possible kernel of A→C does not affect this argument. No determinant
of a hypothetical free cyclotomic module is taken.

## 5. Exact conclusion and grading boundary

Apply Kang–Kashiwara Lemma 4.18 to the ordinary ring B^op (to use its
printed left-module formulation), variable s, the central monic a(s) of
(A), and resolution (E). Its proof uses monicity to split multiplication
by a(s) on each projective over B[s] after restriction to B, and then
splits (E) over B. All of its hypotheses have now been supplied using the independently
checked written ideal equality and the cited balanced QP inputs. Thus the proposed assembly proves F is a finite projective right
B-module: finiteness follows because F is finite over B[s] and is killed
by a monic polynomial.

Parity does not obstruct this conclusion. Given an ordinary B-linear
splitting of an even surjection of supermodules, take its even component;
this is still B-linear on homogeneous inputs and still a splitting.
For a homogeneous degree-zero surjection of integer-graded modules take
the degree-zero component as well. These component operations are defined
on each homogeneous input, whose image has finite support. Thus the
ordinary projectivity yields projectivity in the even graded-supermodule
category, with the shifts already recorded in (Pj); it is not obtained by
pretending that Π^ε B has untwisted left action. No averaging or further
invertibility assumption is required for this component argument.

This settles the square-resolution assembly as a proposed general
right-projectivity argument, not as a reviewed or formalized theorem.
It does not identify a mirror algebra, prove projectivity on the other
side, construct biadjunctions, or show that the prescribed cup–crossing–cap
Rouquier matrix is invertible. Those are separate obligations.
