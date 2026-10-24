# Conditional longest-braid coefficient probes

This is a mathematical reduction supporting the Brundan–Ellis
(arXiv:1701.04133v2), §8 Nondegeneracy
Conjecture. **It assumes all-upward PBW independence with the full abstract `SYM`
coefficients inside SKM.** That input, the action proposed in the other notes in
this directory, and independence for arbitrary oriented matching choices remain
unproved here. The argument below is not a Lean theorem. The ground ring and
scalar data are those of the existing SKM presentation over an even commutative
base; this does not establish an extension to general supercommutative bases.

## Coefficients and endpoints

Write composition right-to-left. Fix a rightmost weight `μ`, upward colour words
`ν, ν′` of length `n`, and

\[
 W=\{w\in S_n:w\nu=\nu'\},\qquad N=\ell(w_0).
\]

Let `A_ν` be the source dot algebra super-tensored with `SYM`, placed in the
rightmost region at weight `μ`. Distinct odd dot variables anticommute, but their
individual squares are not set to zero. The exterior generators of `SYM` do
square to zero; products between distinct exterior generators are retained.
The assumed upward statement is an isomorphism

\[
 E_{\nu,\nu'}:\bigoplus_{w\in W}A_\nu
   \longrightarrow\operatorname{Hom}(U_\nu,U_{\nu'}),
 \qquad (a_w)\longmapsto\sum_w\tau_w a_w.
\]

Here `τ_w a` means the source coefficient followed by `τ_w`, namely `a ≫ τ_w`
in Lean. This is stronger than PBW for the separate quiver-Hecke category.
Initially choose reference reduced expressions. The argument below also handles
other reduced expressions.

For each `w ∈ W`, choose a reduced crossing diagram for `c_w = w₀w⁻¹`. Then

\[
 c_w\nu'=w_0\nu,\qquad
 C_w=\tau_{c_w}:U_{\nu'}\longrightarrow U_{w_0\nu},\qquad
 \ell(c_w)=N-\ell(w).
\]

All complements have the same target; it need not be `U_ν`. Using the assumed
upward expansion in this target block, let `π_top` take the coefficient of one
chosen `τ_{w₀}`. Define

\[
 L_w(f)=\pi_{\mathrm{top}}(C_wf),\qquad
 M_{wv}=L_w(\tau_v).
\]

These maps retain every dot power and bubble coefficient. They are right
`A_ν`-linear: a source coefficient stays at the source under postcomposition
with `C_w`. No assertion of a balanced bilinear pairing over a common
commutative coefficient ring is needed.

## Crossing filtration

Give dots and source bubble coefficients crossing degree zero. The upward
relations have the following properties:

- Distant crossings interchange with sign
  `(-1)^(p(i)p(j)p(r)p(s))`, using the colours at the intermediate word.
- An adjacent braid change has leading coefficient `+1`; its correction
  replaces three crossings by a polynomial with no crossings.
- A quadratic relation removes two crossings. Its unequal-colour term can be
  a nonunit polynomial; the equal-colour square is zero.
- Moving a dot through a crossing has a signed leading term and, when present,
  a correction with fewer crossings. Dot reordering also has its super sign.

These are the upward defining relations. The corresponding existing Lean
filtration lemmas are `far_swap`, `cross_cross_at`, `slide_left_at`,
`slide_right_at` and `braid_at` in
[`QuiverHecke/Straighten.lean`](../../OddMath/QuiverHecke/Straighten.lean).
Their use in this argument does not supply the assumed SKM independence.

Matsumoto moves therefore change a reduced crossing representative only by a
sign and terms of smaller crossing degree. The sign is the product of the
actual distant-interchange signs along a chosen path. The Coxeter word-reduction
procedure, followed by the quadratic relation, reduces a nonreduced word to
strictly smaller crossing degree. Contextual composition and subsequent dot
slides do not increase the number of crossings. Thus a word with `m` crossings
expands only into PBW permutations of length at most `m`; if it is reduced, its
length-`m` part is its permutation with a signed-unit coefficient.

It follows that

\[
 M_{wv}=0\quad\text{if }\ell(v)<\ell(w),\qquad
 M_{wv}=0\quad\text{if }\ell(v)=\ell(w),\ v\ne w,
 \qquad M_{ww}=\epsilon_w1,\quad\epsilon_w\in\{1,-1\}.
\]

Indeed, in the first case the composite has fewer than `N` crossings. In the
second it has exactly `N`, and its permutation is `c_wv`; this equals `w₀` only
when `v=w`. For the diagonal the concatenation is reduced, since its length is
`N` and its permutation is `w₀`. **There is no quadratic factor on the diagonal.**

Order `W` by increasing length. The matrix `M` is upper triangular with diagonal
entries `±1`. Finite back-substitution inverts it over the possibly
noncommutative ring `A_ν`, with products kept in order. No determinant, field,
symmetrizer, finite colour set, or absence of zero divisors is used. The index
set `W` is finite because the boundary length is finite. Consequently

\[
 L E_{\nu,\nu'}=M
\]

is an invertible coefficient transformation.

Other reduced expressions, distinguished points on upward strands, and valid
serializers produce signed triangular changes as well. Sliding dots to the
source gives a signed permutation of their strand-exponent monomials at the
leading crossing degree; every correction lowers that degree. This is a
statement about the underlying coefficient modules, not an assertion that every
change of dot convention is right `A_ν`-linear. Crossing degree is bounded by `N`,
so finite back-substitution still applies despite unbounded dot exponents.
Keep bubbles in the prescribed source placement. Where a homogeneous bubble
is interchanged with a homogeneous diagram, retain the super sign and extend
by homogeneous decomposition.

For example, with distinct odd colours `i,j`, permitted quadratic polynomial
`Q_ij=x₁²+x₂²`, and base `ℚ`, take `ν=(i,j)` and `ν′=(j,i)`. There is one
permutation `s`, and `c_s=1`. Thus `L_s(τ_s a)=a`, including for
`a=δ_iδ_j`. Composing with a reverse crossing instead gives `Q_ij a` and is a
different operation. The odd example cannot be put over `ℤ` with these SKM
scalar data: `Scalars.two_isUnit` requires invertibility of two.

## What is still missing for oriented matchings

Let `B` denote an injective sorting/bending comparison on diagram morphisms,
retaining all its identity and parity-shifted summands. Apply `L` separately to
each upward block, at that block's own weight and boundary. For a matching
choice `F`, write

\[
 T_F=E_{\mathrm{up}}^{-1}B F.\mathrm{expansion},\qquad
 S_F=L B F.\mathrm{expansion}.
\]

Then `S_F=M T_F` blockwise, and

\[
 \ker S_F=\ker T_F=\ker(F.\mathrm{expansion}).
\]

The probes separate diagram morphisms, but they supply no independent rank
information about the formal oriented matching labels. In particular, the
original `SYM` action need not become multiplication by the same coefficient in
every upward block: bending changes the relevant weight and placement.

One cannot keep just the principal sorting-crossing component. For
`0 ≤ m,n < h_i(μ)`, the presentation gives

\[
 \sigma_{ii}\,\mathrm{dcup}_n=0,\qquad
 \mathrm{eps}_m\,\mathrm{dcup}_n=\delta_{mn}\,1_{1_\mu}.
\]

See `cl_invP₄` and `cl_invP₅` in
[`SKM/RelationsNF.lean`](../../OddMath/SKM/RelationsNF.lean).
If the identity is nonzero, the cup direction is nonzero and the crossing kills
it, whereas the cap component detects it. This does not assert that this cup is
an arbitrary chosen reduced matching or give a counterexample to nondegeneracy.
It rules out treating the principal projection as injective.

The remaining transport theorem must compute the leading map on formal
coefficients through cups, caps, every inversion summand, bubble movement at the
changed weights, distinguished points and serializers. Its filtration must
detect every nonzero finite relation, and its leading map must be injective.
Signed-unit pivots would suffice but are not necessary; regular polynomial or
injective block operators would also suffice. Undecorated matching
correspondence or equality of degree and parity does not prove this theorem.

## Finite checks

Run `python3 scripts/Nondegeneracy/nonreturning_complement.py`.
It checks complement lengths and triangular top symbols through `S₄`, all
strand-parity assignments on reduced-expression graphs, and skew/exterior
coefficient arithmetic over `ℚ`. These are finite corroborations of the
argument above, **not** checks of categorical lower terms, the assumed upward
independence, or the unresolved oriented transport.
