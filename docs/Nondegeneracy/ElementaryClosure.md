# Conditional independence at the elementary odd boundary

Fix the SKM datum and permitted scalars over the existing even commutative
base ring. Let `i` be odd, `h_i(μ)=1`, and `λ=μ−α_i`. Use `T_ab`, `K_ab`,
`S`, `e_a`, `H_b`, `J`, `c` and the source coefficient prefix `P_A(p)` from
[ElementarySorting](ElementarySorting.md).

**Conditional conclusion.** If upward PBW with the full coefficient algebra
`SYM` holds in the SKM presentation for `E_i 1_λ` and `E_i E_i 1_λ`, then

\[
 (p_{ab},k_{ab})\longmapsto
 \sum_{a,b}P_A(p_{ab});T_{ab}+P_A(k_{ab});K_{ab}
\]

is injective on finite coefficient families. This is a mathematical reduction
for this fixed family, not a Lean proof of the Brundan–Ellis §8 conjecture.
The ordinary affine quiver-Hecke PBW theorem does **not** supply the stated
upward SKM independence with independent bubble coefficients. Arbitrary
oriented boundaries and arbitrary matching choices remain separate obligations.

## One-strand transport on full SYM

This step works for any colour `j` and weight `λ`, conditional on one-strand
upward independence at that weight. Write `S₀=SYM`, `μ'=λ+α_j`,

\[
 R(p)=\operatorname{rbub}_j(\beta_\lambda(p)),\qquad
 L(p)=\operatorname{lbub}_j(\beta_{\mu'}(p)).
\]

Let `σ_j` be the algebra involution fixing every polynomial generator and
multiplying every exterior generator by `(-1)^|j|`. The defining relations
of `SYM` are preserved. Form the finite coefficient algebra

\[
 A_j=\bigoplus_{a\geq0}x^a S_0,\qquad
 (x^a p)(x^b q)=x^{a+b}\sigma_j^b(p)q.
\]

The upward dot is not square-zero. This is generally not a central polynomial
algebra. With Lean's reversed `End` multiplication, its evaluation is

\[
 \operatorname{ev}(x^a p)=R(p);X^a.
\]

`plcL_right_interchange`, preservation of composition by placement, and
`betaSYM` multiplicativity make this an algebra homomorphism. The stipulated
upward independence makes it injective. The normalized bubble slides put
every `L(p)` in its image: the generator images lie there, corrections lie
in `bubbleSpan = range(betaSYM)`, and the image is a subalgebra. Thus there
is a unique algebra homomorphism `ρ_j:S₀→A_j` satisfying
`ev(ρ_j(p))=L(p)`.

The constant-coefficient map `ct:A_j→S₀` is an algebra homomorphism. Only two
degree-zero terms can contribute to the constant coefficient of a product.
Its composite with `ρ_j` fixes every generator:

| Generator case | Normalized slide and constant term |
|---|---|
| Same even colour | `eq_7_8`: the zero-dot term has coefficient one; every other term has positive dot degree. |
| Same odd colour | `eq_7_10`: the correction powers are `2r`, with coefficients `2r+1`; only `r=0` contributes to the constant term. |
| Distinct connected colours | `eq_7_12_connected`: the leading scalar is `t_ij`; the other dot exponents are `dn j i>0` or `q` with `0<q<dn j i`. |
| Distinct disconnected colours | `eq_7_14_corrected`: the sole term has scalar `t_ij`. |
| Exterior generator | `oddBubble_slide_up`: the normalized odd bubble slides unchanged. |

In both distinct-colour cases the leading scalar cancels **because**
`c_(λ+α_j),i = t_ij c_λ,i`. No normalization `t_ij=1` is imposed. Same-colour
normalization uses `t_ii=1`. The polynomial generator indexed by `n` has
normalized bubble index `n+1` for even colours and `2(n+1)` for odd colours.
By `SYM.hom_ext`,

\[
 \operatorname{ct}(\rho_j(p))=p\qquad\text{for every }p\in S_0.
\]

This includes ordered products of distinct exterior generators. No field,
domain, finite-colour, or additional scalar hypothesis has been introduced.

### The two serializers

The slides above are written with dots followed by a coefficient, whereas
`ev` uses the opposite order. If `ρ_j(p)=∑x^r q_r`, define the **coefficient
sequence**

\[
 \rho_j^+(p)=\sum_r x^r\sigma_j^r(q_r).
\]

Its chronological evaluation is `∑ X^r;R(σ_j^r(q_r))=L(p)` by interchange.
It has the same constant coefficient `p` and sends zero to zero. No algebra
homomorphism assertion about this changed serializer is needed. In all
closure formulas below, `ρ⁺` means this dot-first, coefficient-last sequence;
products of evaluated expressions are chronological, not multiplication
in Lean's `End` algebra.

For a finite family `(p_a)`, the coefficient of degree `n` in the chronological
left-dot-prefix expression `∑ X^a;ρ⁺(p_a)` is

\[
 \sum_{a\leq n}[x^{n-a}]\rho^+(p_a).
\]

If all these coefficients vanish, strong induction on `n` gives `p_n=0`:
earlier inputs have already vanished, the diagonal term is `p_n`, and later
inputs cannot contribute. This neither assumes nor proves that `ρ` is an
automorphism. The additive argument is checked in
[`LeastDotTransport.lean`](../../scripts/NonVacuity/LeastDotTransport.lean),
including a concrete noncommutative matrix-coefficient application.

## The two right-adjunction closures

Write `E=E_i`, `F=F_i`. Every word in the following composites has rightmost
region `λ`; the indicated local regions determine the actual cups and caps:

\[
\begin{aligned}
 R(f)&=(EE\xrightarrow{1_{EE}\eta_\lambda}EEFE
       \xrightarrow{1_E f_\mu 1_E}EFEE
       \xrightarrow{\epsilon_{\mu+\alpha_i}1_{EE}}EE),\\
 R_0(g)&=(E\xrightarrow{1_E\eta_\lambda}EFE
       \xrightarrow{g_\mu1_E}E).
\end{aligned}
\]

These are right-adjunction closures, not `bendF` to an empty target.
Let `X,Y` be the left and right dots on `EE`, `τ` its crossing, and `Z` the dot
on `E`. Use chronological order `τ^ε;X^l;Y^r;[rightmost coefficient]`.
The relations are `XY=−YX`, `X;τ+τ;Y=1`, `Y;τ+τ;X=1`, `τ²=0`.
The even zigzags and `sigmaL` definition give

\[
 R(S)=\tau,\qquad R(e_a;H_m)=Y^a;X^m,
 \qquad R_0(e_a)=Z^a.
\]

Put `χ(b)=b(b−1)/2`. The downward-dot mate contributes `(-1)^χ(b)`;
passing those dots across the odd mixed crossing contributes `(-1)^b`.
Consequently

\[
 R(T_{ab};S)=(-1)^{b+\chi(b)}Y^a;\tau;Y^b,
 \qquad R_0(T_{ab};e_0)=(-1)^{\chi(b)}Z^{a+b}.
\]

The first expression has PBW form

\[
 (-1)^{a+b+\chi(b)}\tau;X^a;Y^b
 +\sum_{j<a}(-1)^{b+\chi(b)+j+j(a-1-j)}X^j;Y^{a+b-1-j}.
\]

In particular `R(u;S)=1−τ;X` and `R(d;S)=−τ;Y`; an unsigned rotation is wrong.

## Middle bubbles and source coefficients

Set `Q₀=1`, `Q_(2n)=SYM.e i (n−1)` for `n≥1`, and
`Q_(2n+1)=δ_i Q_(2n)`. Their normalized evaluations are
`β_ν(Q_r)=c_ν,i⁻¹ bubLs(i,ν,r)`; at `μ` this is `q_r=D;e_r`.
This uses `betaDGen` and `GrassmannianOdd.eq_5_7_a`, including the odd indices.
Let `B_λ(Q)` denote the rightmost bubble. The exact middle-region slide is

\[
 W_r(Y)=\sum_{0\leq t\leq\lfloor r/2\rfloor}
       (2t+1)Y^{2t};B_\lambda(Q_{r-2t}).
\]

Thus `W₀=1`, `W₁=B_λ(δ_i)`, and `W₂=B_λ(Q₂)+3Y²`.
The middle bubble has parity `r`, so

\[
 R(e_a;q_r;H_m)=(-1)^{(a+r)m}X^m;Y^a;W_r(Y).
\]

Using the component formulas in `ElementarySorting` gives

\[
\begin{aligned}
 R(K_{ab};S)
   &=c\sum_{r<b}(-1)^{b+1+r+(a+r)(b-1-r)}
       X^{b-1-r};Y^a;W_r(Y),\\
 R_0(K_{ab};e_0)&=cZ^a;W_b(Z).
\end{aligned}
\]

For homogeneous `p` of parity `e`, `comp_bubAt` gives, for either `F=T_ab`
or `F=K_ab`,

\[
\begin{aligned}
 R(P_A(p);F;S)&=(-1)^{e(a+b+1)}R(F;S);\rho_i^+(p),\\
 R_0(P_A(p);F;e_0)&=(-1)^{e(a+b)}R_0(F;e_0);\rho_i^+(p).
\end{aligned}
\]

In the first line transport is placed only on the **right** strand; it has
no `X` dependence. In both lines it moves the same bubble from `μ` across
`E_i 1_λ`. Extend linearly to inhomogeneous coefficients. Retain the displayed
order `W_r;ρ⁺(p)`; reversing that product silently changes coefficient signs.

## Triangular elimination

Let `θ` be the parity involution of `SYM`. Apply both closures to a finite
relation in the stated family and use upward PBW.

1. Project to the `τ` part. For each fixed left exponent `a`, its row is
   `∑_b (-1)^(a+b+χ(b)) Y^b ρ⁺(θ^(a+b+1)(p_ab))=0`.
   Least-dot detection and the invertibility of signs and `θ` kill every
   through coefficient `p_ab`.
2. Choose the greatest remaining cup exponent `b=B>0`. Its greatest left
   exponent is `B−1`, occurring only when `r=0`. Since `W₀=1` and transport
   has no left-dot dependence, that row is
   `c ∑_a (-1)^(B+1+a(B−1)) Y^a ρ⁺(θ^(a+B+1)(k_aB))=0`.
   Cancel the unit `c` and apply least-dot detection. Descend through `B`.
3. Only `b=0` remains. The second closure is
   `c ∑_a Z^a ρ⁺(θ^a(k_a0))=0`, which kills the remaining coefficients.

This is an injective formal-label comparison, not an inference from an
isomorphism of actual Hom spaces. It establishes the conditional conclusion
at the start, while leaving upward SKM independence and global matching
transport unproved.

## Verification boundary

`python3 scripts/Nondegeneracy/elementary_right_closure.py` checks the through
closure and its explicit PBW expression against termwise closure of the
sorting formula, using formal odd nilHecke rewriting. These finite integer
coefficient checks are not an SKM action over the integers. The middle-bubble,
full-SYM and triangular arguments above are mathematical derivations, not
compiled SKM declarations. Only the general additive least-dot lemma and the
previous first-generator bubble correction have been checked in Lean.
