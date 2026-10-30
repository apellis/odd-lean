# First-order deformed Mackey boundary

**Status: written proof; not a Lean result.** This supplies the first-order
polynomial defect using explicit PBW lifts. The subsequent norm/division
identity is in `DeformedBoundaryDivision.md`; the prescribed tensor-matrix
comparison and its all-height consequence are in `DeformedMatrixComparison.md`.

Source read: KKO I, arXiv:1206.5933v2, §9, diagram (9.5), the following
remark describing B, and equations (9.9)–(9.12), through Lemma 9.5.
The extension to the full coefficient superalgebra below is not attributed
to that paper. Retain the hypotheses and tensor coordinates of
`DeformedSquareResolution.md`: all finite compatible supports, independent
odd parameters, and d_j χ_(j,top)=0 at positive even odd-colour cutoffs.
The calculation below concerns an odd moving colour i. Put d=d_i, p(i)=1,
η=p(β), r=N_i modulo two, ε=η+r; φ is total parity, including coefficients.
At zero cutoff take d=0. All products below are ordered products.

## 1. Operators and the column coordinates

Write R=A⊗ˢR(β), B=R/I, H=A⊗ˢR(β+α_i), e_R=e(β,i), e_L=e(i,β).
Suppress integer grading shifts but retain the shifts Π^ε and Π^r. Then

    L₁=e_R H e_L ⊗_R Π^ε B,    L₀=e_R H e_R ⊗_R B,
    P(h⊗π^ε b)=h f_i(x₁)T⊗b,  T=τ₁⋯τ_n.

The old balance is hι_L(c)⊗π^ε b=h⊗π^ε φ^ε(c)b.
The corrected operator and the target right-dot action are

    ρ(h⊗π^ε b)=(-1)^η h(x₁+2(-1)^r d)⊗π^ε φ(b),
    (h⊗b)t=h x_(n+1)⊗φ(b).                         (1)

These are parity-semilinear for the unchanged right B-action:
ρ(zb)=ρ(z)φ(b). In particular they are not ordinary B-linear maps.
For homogeneous c, moving x₁ or d past ι_L(c) contributes (-1)^|c|;
applying φ on the last factor contributes the same sign. This checks
balance directly, including odd coefficients. Using

    (x₁+2(-1)^r d) f_i(x₁)=f_i(x₁)x₁,

and the moving-dot slide modulo the old cyclotomic ideal gives Pρ=R_t P.
The deletion terms vanish by the old-ideal calculation used for P in
`DeformedSquareResolution.md` §3. Also ρ²=R_s, s=x₁² on L₁:
the cross terms cancel since x₁d=-dx₁, and d²=0. This checks both cutoff
parities without replacing x₁ by the crossing-contraction operator X.

**Checked source operator:** `ELVBoundaryRho.lean` constructs (1) on the
actual full-ELV old-only quotient. `pMap_boundaryRho` proves its first-order
intertwining with P; `boundaryRho_square` proves the square-dot identity.
`boundaryRho_iterate_even` and `boundaryRho_iterate_odd_projection` give all
corrected iterates, and `pMap_boundaryRho_iterate` their prescribed P-images.
This is valid for arbitrary old words, including empty content, and both
cutoff parities. It does not yet construct the extraction (2), the descended
operator (3), or the full boundary (5).

Here are explicit coordinates for the first column. Put U_k=τ_n⋯τ_k
for 1≤k≤n and U_(n+1)=1, and U=U₁. Choose the affine PBW words
adapted to these cosets. The short-coset submodule L₁′ is spanned by

    x_(n+1)^l a U_k e_L ⊗π^ε b,  k≥2,

with compatible word idempotents and a in the old algebra on the first
n positions. The remaining coset is k=1. The quotient V₁ has the free
right B polynomial coordinates v_l=t^l T_i^N ⊗π^r 1, and extraction is

    B₁(x_(n+1)^l a U_k e_L⊗π^ε b)
       = δ_(k,1) v_l φ^r(a)b.                       (2)

The symbol T_i^N records the source coefficient twist; it is not the
crossing product T. Formula (2) includes total coefficient parity. Indeed
moving a through U in the longest coefficient contributes φ^η(a), then
tensor balance contributes φ^ε, giving φ^r(a). All other terms are short
cosets. This also explains why suppressing Π before extracting coefficients
would give the wrong twist.

Right multiplication by x₁ preserves every short-coset span: U_k, k≥2,
fixes position one, so x₁ passes through it up to the far-dot sign and
becomes an old dot in a. Multiplication by d preserves it as well.
Consequently ρ(L₁′)⊆L₁′. On the long coset, sliding x₁ through U gives
(-1)^η x_(n+1)U plus short cosets. Formula (2) therefore gives

    ρ̄(v_l b)=v_(l+1)φ(b)+2v_l d φ(b).              (3)

For the correction, h d⊗π^ε φ(b)=(-1)^ε h⊗π^ε dφ(b);
the prefactor is 2(-1)^(η+r+ε)=2. Thus the coefficient correction in
(3) has the SAME plus sign at both cutoff parities, despite (1).
This is a useful normalization check. Direct substitution in (3) yields
ρ̄²(v_l b)=v_(l+2)b.

## 2. Factorization through the polynomial quotient

Let L₀′ and F be the source crossing tensor and its injection. Affine
Mackey PBW, extended to A and then tensored with B, gives the split
right-module decomposition

    L₀=F(L₀′) ⊕ j(V₀),       V₀=⊕_(l≥0) t^l B,
    j(t^l b)=x_(n+1)^l e_R⊗b.                       (4)

It remains split after tensoring because the affine decomposition is an
explicit direct sum, not an appeal to flatness. Write C₀ for its polynomial
projection. The crossing map is F(a⊗π b)=aτ_n⊗b.

We check C₀P(L₁′)=0 on the displayed short generators, rather than assuming
a deformed commutative diagram. For k≥2, U_k supercommutes with f_i(x₁),
which is homogeneous of parity r. Thus their image under P has the form

    ± x_(n+1)^l a f_i(x₁) U_k T ⊗b.

The far last dot supercommutes with a f_i(x₁); moving its power to the
right leaves a f_i(x₁) as a left old-algebra factor. C₀ is left R-linear,
and the image of a f_i(x₁) in B is zero on these corners. Therefore its
polynomial projection is zero. This proof also covers odd a and independent
odd coefficient factors. It uses homogeneity, not centrality of f_i.
There is consequently a uniquely defined map

    A_∂:V₁→V₀,       C₀P=A_∂B₁.                  (5)

It is right B-linear. This assertion alone does not identify all the other
quotients of diagram (9.5). `DeformedCyclotomicTopRow.md` supplies the
proposed written top-row identification: restrict P through the specified
short-column inclusion, identify its multiplier with the lower-height
balanced resolution, and use right exactness only for its cokernel.
Its descended vertical arrow is the prescribed a tau_n b, with total
coefficient parity. That additional argument is not yet Lean-checked or
independently accepted.

### Checked ordinary-polynomial short-image inclusion

`AppendContentShortImage.lean` proves the inclusion used with (4):
`appendContentP_short_mem` sends every element of the prescribed short source
into the prescribed F range, without an affine factorization hypothesis.
`projected_short_multiplier_sum` first applies the left append projector to
the entire PBW multiplier: final old colours unequal to i vanish. Each
surviving matrix entry factors by `appendShortEntry_factor`. Append PBW on
its old factor gives `appendLeftSum`; the lower-height coefficient crosses
τ with twist parity p(i)p(i), retaining the original right tensor coefficient.
The content parameter n means old height n+1, including height one at n=0;
cutoff zero is allowed. This checks only the ordinary-polynomial specialization,
not full ELV coefficients or the reverse inclusion. `AppendContentBoundary.lean`
now assembles the ordinary content `MackeyCosets` and `toMackeyBoundary`
using this forward inclusion. It identifies both extraction maps with their
PBW coordinates, proves (5), and proves both identities in (8) for the
normalized lifts. No monicity assumption is used. Full ELV coefficients,
old height zero and the subsequent norm comparison remain separate.

## 3. Explicit lifts and first-order defect

Define z₀=Ue_L⊗π^ε1 and z_k=ρ^k(z₀). These are specified elements of
the balanced module, not lifts selected by an existence assertion. More
explicitly, for q≥0,

    z_(2q)=Ue_L x₁^(2q)⊗π^ε1,
    z_(2q+1)=(-1)^η Ue_L x₁^(2q)(x₁+2(-1)^r d)⊗π^ε1.

Their extracted coordinates w_k=B₁z_k are

    w_(2q)=v_(2q),
    w_(2q+1)=v_(2q+1)+2v_(2q)d.                    (6)

Thus the w_k form a right B-basis: the inverse triangular change replaces
+2d by -2d in each adjacent even/odd pair. Define a right B-linear section
ℓ(w_k b)=z_k b, extended over finite sums. It satisfies

    B₁ℓ=1,       ρℓ=ℓρ̄,
    ρ̄(w_k b)=w_(k+1)φ(b).                        (7)

This is the missing compatible-lift construction on the PBW quotient.
Use the unique decomposition (4) to DEFINE ψ and A_∂ by

    Pℓ(v)=Fψ(v)+j(A_∂v).

When n=0 the crossing modules are zero, U=1, and E=X=0; all the
formulas below retain that interpretation. For n>0, on L₀′ retain exactly
the source operators

    X(a⊗π b)=-a x_n⊗π φ(b),   E(a⊗π b)=aφ(b).

Their equal-colour dot slide is

    F(u)t=F(Xu)+j(Eu),

and j(f)t=j(ft). Applying Pρ=R_tP to (7), and comparing the two
components of (4), proves for every finite v∈V₁

    ψ(ρ̄v)=Xψ(v),
    A_∂(ρ̄v)-A_∂(v)t=Eψ(v).                       (8)

The right side lies in degree zero in the polynomial variable. In
particular φ_k=A_∂(w_k), ψ_k=ψ(w_k) satisfy
φ_(k+1)=Eψ_k+φ_k t and ψ_(k+1)=Xψ_k. The source coordinate w_k, not
v_k at odd k, is the corrected coordinate for this recurrence.

## 4. The subsequent division step

Equation (8) is first-order information and is stronger than square-linearity.
It does NOT yet prove the leading-degree conclusion of KKO Proposition 9.3.
To apply its Lemma 9.5 one must calculate, in the coordinates (6),

    A_∂(S_i(ρ̄)w₀)

and its iterates with the full ordered coefficients, where S_i has factors
(t²-x_a²)² at repeated odd colours. Equivalently one must re-extract the
coefficient of U from g_n⋯g₁ with the full deformed f_i and the φ^r
coefficient twist, and compare it with these corrected lifts. This norm
comparison is supplied in `DeformedBoundaryDivision.md`. The known QP factor t²+x_a² is
not S_i, and cannot substitute for it. Nor does (8) alone bound the initial
values A_∂(w_k). No leading-degree formula, matrix inverse, reverse
adjunction, left projectivity, field specialization or Frobenius trace is
asserted in this note.