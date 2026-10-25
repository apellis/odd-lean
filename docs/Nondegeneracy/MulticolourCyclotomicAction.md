# Super coefficient cyclotomic towers: mixed inversion and connected transfer

Research toward Brundan–Ellis §8. These are written algebraic arguments and
finite diagnostics, not checked Lean theorems or a constructed SKM action.
The source for the mixed argument is Kang–Kashiwara–Oh,
[arXiv:1206.5933v2](https://arxiv.org/pdf/1206.5933v2), §7.1, Theorem 9.1
and its ideal identity (9.3), pp. 46–47. Their printed coefficient restriction
in (7.1) excludes odd-index coefficients at odd colours. The extension below
explains why that restriction can be replaced for this particular argument;
it does not import their entire cyclotomic theorem under new hypotheses.

## Mixed EF inversion survives homogeneous odd coefficients

Let `A` be a supercommutative coefficient algebra over the existing even
ground ring, and use the explicit super tensor extension `A ⊗̂ R(n)` of
the affine QH superalgebra. Choose a cyclotomic polynomial at each colour,

`f_i(x)=Σ_l c_i,l x^(N_i−l)`, with `|c_i,l|=l p(i)`.

Integer degrees can also be imposed if graded functors are wanted. The ideal
is generated idempotentwise by `f_(ν1)(x1)e(ν)`. Each such generator is
homogeneous of parity `N_(ν1) p(ν1)`, even when the sum over different first
colours is not homogeneous.

If `k≥2`, the crossing `τ_k` preserves the first colour and is distant from
`x1`. Moving it past a summand of the cyclotomic generator contributes the
sign from its coefficient and the sign from its dots. Their product is

`(−1)^(|τ_k| (|c_i,l|+(N_i−l)p(i)))
 = (−1)^(|τ_k| N_i p(i))`.

Thus the whole generator commutes with that distant crossing up to a single
unit sign, exactly the fact cited from (7.1) in KKO's proof. The same argument
applies to distant dots and homogeneous coefficient elements. It is crucial
to include the coefficient sign: treating `c_i,l` as even makes the signs
term-dependent and invalidates this argument.

Write `R` for the extended affine algebras, `f=f(x1)`, and let `R(n,1)`
preserve the last strand. The usual affine Mackey decomposition and the
preceding distant commutations give the same ideal expansion as KKO:

`R(n+1) f R(n+1)` is the sum of

* `R(n+1) f R(n,1)`;
* `R(n,1) f R(n+1)`;
* `R(n,1) τ_n...τ_1 f τ_1...τ_n R(n,1)`.

All signs are taken idempotentwise and are units, so do not change these
submodule sums. In the third summand the crossing word carries the last
strand to the first position and back. It cannot change its colour, while
both outside `R(n,1)` factors preserve that last colour. Therefore its
component between different last colours `i≠j` is zero. The resulting
identity is precisely the extension of (9.3): the two-sided cyclotomic
ideal in that mixed corner is the sum of the ideals imposed from the two
`R(n)` sides.

Apply the two cyclotomic quotient tensors to the affine mixed Mackey
isomorphism, KKO (9.2). The preceding ideal identity identifies its left
side with the mixed corner of the full cyclotomic quotient. Its right
side is the tensor product of cyclotomic induction/restriction bimodules.
Consequently the mixed functor isomorphism of Theorem 9.1 extends:

`E_i F_j ≅ Π^(p(i)p(j)) F_j E_i`, for `i≠j`,

with KKO's `q^(−(α_i|α_j))` shift when integer gradings are retained.
No coefficient-flatness hypothesis is needed for this argument: tensoring
an existing isomorphism preserves it, and quotient tensor products are
right exact. Affine Mackey itself extends by the explicit super tensor
base extension. This statement concerns bimodules and functors on all
modules; preservation of projectives, exactness of induction, and the
same-colour inversion matrix are additional obligations.

## Connected degree-two transfer preserves the ELV coefficient constraint

Use the ELV coefficient algebra from [arXiv:2203.14153v2](https://arxiv.org/pdf/2203.14153v2),
§3.5, (3.24). In degree `N`, put `m=floor(N/2)`, with even elementary
parameters `χ_1,...,χ_m`, odd `d`, and relations `d²=0` and additionally
`dχ_m=0` for even `N`. Put `χ_0=1`. Their polynomial is

`a^N(x)=Σ_(l=0)^N (−1)^l x^l c_(N−l)`,
`c_(2r)=χ_r`, `c_(2r+1)=dχ_r`.

For the connected two-odd-colour datum with off-diagonal entries `−2`, take
`Q_ij(x,y)=x²+y²` and write `z=y²`. The following coefficient transfer is
well-defined into `A_N[z]`:

`A_(N+2) → A_N[z]`,
`χ'_r ↦ χ_r+zχ_(r−1)`, `d' ↦ d`,

where omitted old elementary generators are zero. If `N` is even, the new
top relation maps to `d(zχ_m)=z(dχ_m)=0`. In odd degree there is no such
top relation. Thus the map retains the odd parameter and its products with
independent other-colour exterior parameters.

Under this transfer,

`a^(N+2)(x) = (x²+z) a^N(x)`.

For odd `N` this is a literal polynomial identity in fixed normal order.
For even `N`, before imposing the old top relation the difference is
`−x dχ_m`, and the ELV relation kills exactly that residual. Therefore the
top relation is part of the compatibility mechanism, not a disposable
technical constraint. Multiplication by the connected quadratic increases
the degree by two, matching the magnitude of the relevant Cartan shift;
which induction/restriction direction uses this transfer still has to be
identified in the actual tower.

`scripts/Nondegeneracy/elv_connected_transfer.py` checks degrees 1 through
10, the top-constraint image, uniform distant-crossing parity, and negative
controls for omitting either the coefficient sign or the top relation.
The ring map alone does not construct the required trace or same-colour
inversion. In particular it does not identify the transferred parameters
with normalized categorical bubbles.

## Next boundary: same-colour inversion and projectivity

KKO's Theorem 9.6 uses Proposition 9.3's monicity and the exact diagram (9.5),
which depends on the earlier cyclotomic projectivity/exactness results.
The mixed argument above does not establish those ingredients with odd
coefficients. A nilpotent exterior deformation can lift an invertible
matrix once the deformed source and target are known to be finite free
with compatible reductions; freeness is an additional theorem, not a
consequence of the bounded-separation estimate. The immediate target is
therefore the specific ELV-compatible multicolour bimodule construction
and its monic division/projectivity argument, not another isolated upward
crossing test.

## Even cutoff: an exact normality repair for the first bimodule map

The obstruction to copying the same-colour proof is visible already in
KKO (8.3), third identity, and the right-`t_i` linearity claimed for `P` in
(8.5). At `β=0`, that map is simply `P(b)=b f(x)`. Its original source
right-dot action requires `x f=f x`. This fails for the even ELV polynomial:
for example `f=x²−xd+χ_1` has `x f−f x=−2x²d`, generally nonzero.
This remains nonzero after specializing the top coefficient `χ_1` to zero.
Thus that specialization helps the coefficient ring but does not remove
the required bimodule twist.

There is an exact repair at this first stage. Let `N=2m≥2`, let `A_N` be
the ELV coefficient ring, and form the skew polynomial algebra
`B=A_N[x;parity]`, so `x a=(−1)^|a| a x` for homogeneous coefficients.
Write

`f=χ_m+(x²−xd)q(x²)`,

where `q` has even coefficients. The defining relation `dχ_m=0` gives

`x f=f(x−2d)`, `a f=f a` for every coefficient `a∈A_N`.

Define the even algebra automorphism `ν` by

`ν(x)=x−2d`, `ν(a)=a` on coefficients.

Its inverse sends `x` to `x+2d`; it preserves `x²` and fixes `f`. The
normality identities give `b f=f ν(b)` for every `b∈B`. Consequently
multiplication by `f` is a bimodule map from `B` with its **right action
twisted by `ν⁻¹`**, to ordinary `B`:

`P: {}_1 B_(ν⁻¹) → B`, `b↦b f`.

Indeed `ν⁻¹(a)f=f a`, so `P(b⋅a)=P(b)a`. In particular the repaired source
right-dot action is multiplication by `x+2d`, not `x−2d`. This direction
is forced by the source map convention in (8.5).

Since `f` is monic in the skew variable, right multiplication by `f` is
injective by comparison of leading coefficients, even when `A_N` has zero
divisors. Its image `Bf=fB` is the two-sided cyclotomic ideal. Monic division
therefore yields the exact sequence of even superbimodule maps

`0 → {}_1 B_(ν⁻¹) → B → B/(f) → 0`,

and `B/(f)` is free over `A_N` on the dot powers `1,x,...,x^(N−1)`.
This supplies the `β=0` twisted replacement for the start of KKO §8;
it is not yet their all-`β` projectivity theorem.

For odd cutoff the analogous normalizer also sends `d` to `−d` and fixes
even coefficients; the identities still hold. The independent spectral
stream is investigating the simpler odd-cutoff dot translation. The present
same-colour task concentrates on even cutoff, where translating the dot
does not remove its exterior coefficient.

`scripts/Nondegeneracy/elv_normality.py` checks the exact skew-polynomial
identities for `N=1,...,8`, including `ν(f)=f`, preservation of squares,
the inverse automorphism, and noncommutation controls at even cutoff.
The pending all-`β` task is to replace the right-dot action in KKO's `K1`
by the transported inverse twist, reconstruct `P,Q` and the commutative
diagram in Corollary 8.6, and prove its projectivity statement. KKO's `F_i`
in the proof of Proposition 9.3 also need not commute with `t_i` after
deformation; its `S_i` remains built from even squared-dot differences.
Monic skew division is still available, but the source bimodule identities
must be re-established before importing that proof.

## First connected inversion corner: no existing strand of colour i

There is a concrete connected case beyond the `β=0` normality lemma. Take
two odd colours with `a_ij=a_ji=−2`, `Q_ij(t,x)=t²+x²`, even ELV cutoffs
`N_i,N_j`, and independent exterior parameters `d_i,d_j`. Let
`β=α_j` and put `B=R^Λ(α_j)`, including the coefficient algebra. There is
no removable `i` strand, so `F_i E_i` is zero in KKO's convention.

The corner of the two-strand cyclotomic algebra ending in `i` is

`e(ji) R^Λ(α_i+α_j) e(ji) ≅ B[t;parity]/(f_i(t)(t²+x_j²))`.

Here is the ideal argument, which is necessary for identifying this with
the cyclotomic corner. The affine `ji` corner has only dot PBW terms:
the two colours are distinct, so the only permutation returning this word
to itself is the identity. The cyclotomic generator on `ji` imposes
`f_j(x_j)=0`. The generator on `ij` contributes through an off-diagonal
crossing on each side. Mixed dot transport takes it to `f_i(t)` and the
two crossings compose to `Q_ij(t,x_j)`. All other terms are polynomial
multiples of these, by the distinct-colour PBW descriptions of the two
off-diagonal corners. Thus the full corner ideal is exactly generated
by the two displayed polynomials; it is not legitimate to impose
`f_i(t)=0` alone.

The variable `x_j²` is even and central in this one-colour base. The product
`f_i(t)(t²+x_j²)` is monic of degree `N_i+2` and normal under the same
inverse-dot twist as above: the twist fixes both squares. Consequently
this corner is free over `B` on `1,t,...,t^(N_i+1)`. The canonical induction/
restriction unit is inclusion of `B` in this corner; its successive extra-dot
powers therefore give an isomorphism from these `N_i+2` identity summands
to `E_i F_i`. Their right/left coefficient signs are exactly the parity
twists coming from `t^r b=(−1)^(r|b|) b t^r`.

This is the positive-weight same-colour inversion at this particular
connected object: `h_i(Λ−α_j)=N_i+2`. It uses the actual cyclotomic corner
and canonical unit/dot maps, not a freely chosen matrix. It does not provide
the next case with an existing `i` strand, where the `F_i E_i` summand is
nonzero and the full Mackey/intertwiner argument becomes necessary.

For the minimal specialization `N_i=N_j=2`, with top even parameters zero,
`connected_first_inversion.py` verifies the resulting 32-dimensional algebra.
Its normal forms are `d_i^a d_j^b x_j^c t^r`, with `a,b,c<2`, `r<4`.
All 32 intersecting rewrite ambiguities agree; reduction decreases dot
count or sorting inversions. The canonical unit/dot basis matrix is invertible,
the mixed exterior product has rank 8, and `f_i(t)` itself remains nonzero
(a control against imposing the wrong cyclotomic relation).

Separately, `elv_kko_first_map.py` checks the right-dot twist at
`β=α_j`: with `f=x²−xd`, the exact identity is
`−(x+2d)fτ=fτy`. It also checks that the old `j` cyclotomic relation maps
to the correct target left ideal, retaining a second independent parameter.
At `β=α_i` the right-dot residual is `−f`, in the defining left ideal.
For that same-colour case the script gives an explicit PBW left-ideal
witness for KKO (8.18) in degree two. These tests support the proposed
all-`β` repair but do not replace its bimodule and projectivity proof.
