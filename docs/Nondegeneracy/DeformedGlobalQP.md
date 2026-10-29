# Deformed all-prefix QP calculation

**Status: proposed written proof; not a Lean theorem.** This supplies an
all-prefix argument for equation (3) of `DeformedProjectiveResolution.md`
and an old-generator balance argument for P. It does not construct an exact
projective resolution or prove the ideal-sum assertion.

Use the full coefficient algebra A and polynomials f_j of that document,
including d_j χ_top=0 at positive even odd-colour cutoffs. Work on finite
compatible support in an arbitrary symmetrizable Cartan superdatum, over a
purely even commutative ring with 2 invertible and the prescribed KKO scalar
parameters. No independence of simple roots, finite type, or flatness of a
cyclotomic block is used. All parity automorphisms below act on A as well.

The source comparison read here is KKO I, arXiv:1206.5933v2, pp. 39–44:
(8.3)–(8.5), Lemma 8.3, Proposition 8.4, and the proof of Theorem 8.5,
especially (8.14)–(8.17). The extension to odd coefficients is an argument
below, not a theorem attributed to that source.

## 1. Quotients and cancellation

Put H_n=A⊗ˢR(β+α_i), with |β|=n. Write F_r for the colour-dependent
first-position cyclotomic polynomial placed at position r. In particular,
F_r e(μ)=f_(μ_r)(x_r)e(μ). Let R_1(β) be the old algebra on positions
2,…,n+1 and set

    J_n=H_n F_2 R_1(β),     M_n=H_n e(i,β)/J_n e(i,β).

This is the first-position polynomial balanced quotient, not the quotient
which imposes the moving relation F_1. The old ideal is two-sided in
R_1(β); thus the displayed left submodule includes arbitrary old factors
on both sides of F_2. Parity twisting the balanced coefficient factor does
not change this vanishing submodule.

For the cancellation step assume n > 0; the empty-prefix base case is
separate, since its displayed last-minus-first difference would be zero.
Use affine right PBW coset coordinates before tensoring with the old
cyclotomic block B. Tensoring that direct-sum isomorphism gives polynomial
coordinates with coefficients in B, without assuming B is A-flat. In these
coordinates right multiplication by x_(n+1)^2−x_1^2 has leading moving-dot
term −x_1^2, with unit coefficient and no crossing mixing. Hence it is
injective by the largest moving exponent. At an even moving colour the
same argument applies to x_(n+1)−x_1. These right operators preserve the
balanced quotient: the old dot acts on B and the moving square commutes
with the old algebra. This is the multicolour version of the checked local
right-PBW argument, not cancellation in a cyclotomic algebra in which the
moving dot has already been specialized.

**Checked cancellation ingredient.** `ELVPrependDescent.lean` now supplies
the actual full-ELV old-Hom coordinate equivalence, not just an affine
raw-index surjection. In `ELVMovingShift.lean`,
`movingSquare_coordinate_shift` and `movingEvenDot_coordinate_shift`
identify actual source precomposition with the exponent shifts.
`oldSourceTarget_pair` and `oldSourceTarget_above` prove preservation of
that filtration by the actual old action. Finite support then proves
`lastDotSquareDifference_injective` and `lastDotEvenDifference_injective`.
`lastDotDifference_projection` identifies those quotient maps with the
positioned differences above for n > 0. This closes the cancellation
ingredient only; the all-prefix calculation below is not thereby a Lean
theorem.

## 2. The relation-killing step for every prefix

Fix ν=(ν_1,…,ν_n), put

    T_r=τ_1⋯τ_r,     V_r=g_r⋯g_1,
    D=x_(n+1)^2−x_n^2,     E=x_(n+1)−x_n.

Products act on their rightmost idempotent first. Thus V_n moves the first
i-strand to position n+1; T_n brings it back. In particular T_(n−1)V_n
has left word (ν_n,ν_1,…,ν_(n−1),i).

The affine pitchfork relation τ_a g_(a+1)g_a=g_(a+1)g_a τ_(a+1), together
with distant supercommutation, gives

    T_(n−1)V_n e(i,ν)=σ V_n (τ_2⋯τ_n)e(i,ν),       σ∈{1,−1}.

This is an affine identity. One obtains it by moving the rightmost τ of
T_(n−1) through the adjacent pair of g's, then the next τ, until none
remain on the left; distant swaps supply σ. No polynomial has been moved
through a bare crossing in this step.

Suppose ν_n=i. The left word above then starts in i. Each f_j is
homogeneous of parity p(j)N_j. Intertwiner transport moves both its dots
and its coefficients, so

    f_i(x_1) T_(n−1)V_n e(i,ν)
       = σ' V_n F_2 (τ_2⋯τ_n)e(i,ν) ∈ J_n.             (K)

Indeed τ_2⋯τ_n first moves ν_n=i to old position 2, so the polynomial
there is exactly f_i, not f_(ν_1). This specifies the intermediate ideal
and the position where it vanishes. It is the deformed version of (8.17).
The sign σ' is immaterial for vanishing; no such unspecified sign is used
in the surviving QP calculation below.

**Checked full-coefficient relation killing.** `ELVPrefixKilling.lean`
proves `ELVOld.allPrefix_relation_context` using the actual `moveHom` and
`lastToFirstHom`. It includes every prefix `μ`, spectator word `σ`, cutoff,
and moving-colour parity, with an arbitrary ambient continuation in the
full ELV category. The stronger `projection_prefix_relation_context`
allows an arbitrary full-coefficient old Hom before its relation.
`insert_comp_move` derives the needed naturality from
`hom_comp_moveHom`, with the twist on total coefficient-plus-diagram
parity. `ELVOldRightContext.lean` proves right-context composition,
relation preservation, and containment of the extended old ideal.
Vanishing therefore takes place in the actual old-only quotient, not in
an ordinary polynomial specialization or an assumed relation-killing
package. This establishes (K); the signed repeated-colour induction in
§3 is not yet supplied by these declarations.

## 3. Induction, with the surviving signs

Let A_(ν<) denote f_i(x_1) times the required product for ν_1,…,ν_(n−1).
The induction hypothesis is

    f_i(x_1) T_(n−1)V_(n−1) e(i,ν) ≡ A_(ν<) e(i,ν) mod J_n.

It follows from the smaller quotient by adjoining the last spectator:
its old first-position ideal is contained in J_n. Set V=V_(n−1).

If ν_n≠i, τ_n g_n is Q_(i,ν_n)(x_n,x_(n+1)). Transport this polynomial
through V, not through T_(n−1), obtaining

    Q_(i,ν_n)(x_n,x_(n+1)) V
       = V Q_(i,ν_n)(x_1,x_(n+1)).

Here the KKO parameter parity conditions make every monomial's transport
sign trivial (odd-colour variables occur to even powers). The induction
hypothesis gives the required extra Q factor.

If ν_n=i is odd, put h=p(ν_1)+⋯+p(ν_(n−1)) modulo 2 and
D_0=x_(n+1)^2−x_1^2, E_0=x_(n+1)−x_1. The exact transport laws are

    D V=V D_0,      E V=(−1)^h V E_0.

The second includes the spectator's supercommutation with V. Use

    g_n=(E−τ_n D)D,       τ_n g_n=τ_n D E.

Define Z=f_i(x_1)T_(n−1)τ_n D V. Equation (K), before cancellation, is

    Z D_0 ≡ (−1)^h A_(ν<) E_0 D_0.

Cancel the right operator D_0 in M_n. Then the desired product is

    f_i(x_1)T_n V_n
      = (−1)^h Z E_0
      ≡ A_(ν<) E_0²
      = A_(ν<)(x_1²+x_(n+1)²).

Thus the two signs cancel. This does not move f_i past τ_n and does not
cancel f_i or any coefficient.

If ν_n=i is even, use D=x_(n+1)−x_n and D_0=x_(n+1)−x_1 instead.
The local formulas are g_n=(1−τ_n D)D and τ_n g_n=τ_n D.
Equation (K) says

    (f_i(x_1)T_(n−1)τ_n D V−A_(ν<))D_0 ≡ 0.

Cancel D_0. There is no additional factor. The empty word starts the
induction. This proves the proposed quotient identity

    f_i(x_1) T_n V_n e(i,ν)
      ≡ f_i(x_1) ∏_(ν_a≠i) Q_(i,ν_a)(x_1,x_(a+1))
                     ∏_(ν_a=i odd)(x_1²+x_(a+1)²)e(i,ν).

All products added during induction are even, so their order introduces
no further super signs. Zero cutoffs and either parity of N_i are included.

## 4. Old-generator P balance

This is a separate calculation in K₀, where the old algebra occupies
positions 1,…,n. Write I₀=H_n F_1 R(β)e(β,i), W=F_1 T_n e(β,i),
and ε=p(i)(N_i+p(β)). The needed equation for homogeneous old b is

    ξ(b) W ≡ (−1)^(ε|b|) W b mod I₀.                 (P)

For coefficients c∈A it holds exactly: W has parity ε, and c is
supercentral. For idempotents it is exactly the strand permutation.
For dots and crossings the following describes the error terms explicitly;
it is useful also when coefficients have odd parity.

Sliding x_(a+1) through F_1 T_n produces the main signed term W x_a.
Its only possible error is supported where ν_a=i and is, up to a sign,

    F_1 τ_1⋯τ_(a−1) τ_(a+1)⋯τ_n.

Move the second crossing string left past the first (their indices differ
by at least two) and past F_1 (its indices are at least two). What remains
on the right of F_1 lies in R(β), so this error lies in I₀.

Sliding τ_(ℓ+1) through the long string produces W τ_ℓ. The only error
is the local braid correction, a polynomial C on positions ℓ,ℓ+1,ℓ+2,
with shape

    F_1 τ_1⋯τ_(ℓ−1) C τ_(ℓ+2)⋯τ_n.

Write L=τ_1⋯τ_(ℓ−1) and S=τ_(ℓ+2)⋯τ_n. For a polynomial p the
dot-crossing relations give pτ_a=τ_a p'_a+p''_a, componentwise, with
polynomials p'_a,p''_a retaining all coefficient signs. Induction through
the fixed tail S therefore gives C S=Σ_u u p_u, where u is a subword
of S and p_u is polynomial. No new crossing index or braid move is needed.
Every crossing of u has index at least ℓ+2, so u supercommutes past L
and F_1. Expand p_u=Σ_k x_(n+1)^k q_(u,k), with q_(u,k) involving only
the first n dot positions and coefficients. Since ℓ≤n−1, the moving
power also supercommutes past L and F_1. Thus, on homogeneous components,

    F_1 L C S e(ν,i)
      = Σ_(u,k) ±(u x_(n+1)^k) F_1 (L q_(u,k)) e(ν,i) ∈ I₀.

The boundary dot x_ℓ stays in the residual old-algebra right factor;
it never needs to cross τ_(ℓ−1). No division is used.

The sign of each main term is (−1)^(ε|b|): the old generator crosses the
moving-strand crossings with total parity p(i)p(β), and crosses the
homogeneous F_1 with parity p(i)N_i. The local relations give the same
sign when a participating strand is odd. For a monomial coefficient of
F_1, its coefficient parity and dot parity sum to p(i)N_i; treating only
the dots would give the wrong sign. Thus the coefficient-extended version
of the old-generator congruences (8.3) uses total parity, and products and
sums of generators give (P).

There is one additional descent check: the old cyclotomic ideal acts by
zero. In (P), set b to an old first-position relation. Its right side
vanishes in K₀ by construction, proving the required left balance after
passing to B. With Π^ε B carrying left action b·π^ε c=π^ε φ^ε(b)c,
(P) gives P(h⊗π^ε c)=hW⊗c. This is old-algebra balance, not unchanged
right-t linearity. At odd colour the normalizer also changes x to x−2d_i;
at odd cutoff it acts by parity on coefficients. Only the square variable
is fixed in both cases.

## 5. Boundary of the conclusion

The calculation does not prove the deformed analogue of Lemma 8.2 (the
ideal-sum equality). In particular it does not yet identify the cokernel
of P with the induction corner, nor supply all projective B[s] module
structures and their exact sequence. The central-monic projectivity lemma
cannot be invoked until that exact projective sequence has been proved.
The QP formula and P balance alone do not establish projectivity or the
multicolour action; the stated remaining inputs are essential.
