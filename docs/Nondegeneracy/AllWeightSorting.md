# All-weight target sorting and the source-side threshold

This extends the fixed-family calculation in
[ElementaryClosure](ElementaryClosure.md) to both colour parities and all
coroot weights. Its conclusion is still **conditional on upward SKM PBW
with full SYM**, not ordinary affine PBW, and still concerns the prescribed
through/cap-cup family. It does not establish arbitrary-context sorting or
independence for every `MatchingBasisChoice`.

Composition is chronological. Fix a colour `i`, weight `μ`, and put
`h=h_i(μ)`, `ε=|i|`, `t=(-1)^ε`, `c=c_μ,i`, `λ=μ−α_i`.
Retain `A=EF1_μ`, `B=FE1_μ`, `S:A→B`, `L:B→A`, `e_a:A→1_μ`,
`H_m:1_μ→B`, `u=uLM`, `d=dRM` and `x=uRM` from `LeftDot`.
Let `J=etaP:1_μ→A`; its parity is `ε(h+1)`.
The fixed families are

\[
 T_{ab}=u^a;d^b,\qquad K_{ab}=e_a;J;u^b\quad(a,b\geq0).
\]

## Target components and normalized loops

The target-side component map and its reconstruction are

\[
 f\longmapsto(f;S,(f;e_s)_{0\leq s<h}),\qquad
 f=-(f;S);L+\sum_{0\leq s<h}(f;e_s);\operatorname{dcup}_s.
\]

The tuple is empty if `h≤0`. This follows from `eq_2_12_a`, but does not
alone prove coefficient injectivity.

Choose `Q_n∈SYM` with `Q_n=0` for `n<0`, `Q₀=1`, and
`β_ν(Q_n)=c_ν,i⁻¹ bubLs(i,ν,n)`. Explicitly, for even `i` and `n>0`,
`Q_n=SYM.e i (n−1)`. For odd `i`, use
`Q_(2r)=SYM.e i (r−1)` for `r>0` and `Q_(2r+1)=δ_i Q_(2r)`.
Write `q_n=β_μ(Q_n)`. The actual bubble definition gives

\[
 J;e_r=cq_{r-h+1}.
\]

Thus the loop vanishes for `r<h−1`, and equals `c` times the identity at
`r=h−1` whenever that dot count exists.

## Uniform target-cup formulas

With sums understood to be empty when their upper limit is negative,

\[
\begin{aligned}
 K_{ab};S&=-c\sum_{n=0}^{b-h}
       t^{b-h+1-n}e_a;q_n;H_{b-h-n},\\
 K_{ab};e_s&=c\,e_a;q_{b+s-h+1}.
\end{aligned}
\]

Here is the negative-weight step that cannot be omitted. The dot slide
`S;x−t u;S=e₀;H₀` gives

\[
 J;u^b;S=t^b J;S;x^b-
     \sum_{r=0}^{b-1}t^{b-r}(J;e_r);H_{b-1-r}.
\]

For `h>0`, `J;S=0`. For `h≤0`, put `N=−h` and
`C_j=cl(dcapL i j)`. The actual `etaP` definition and opposite inversion
block instead give

\[
 J;S=t^{h+1}c\left(\sum_{j=0}^{N-1}(H_N;C_j);H_j-H_N\right).
\]

The negative branch of `bubL` identifies
`H_N;C_j=−t^(h−j)q_(N−j)`. Consequently

\[
 J;S=-c\sum_{n=0}^{N}t^{N+1-n}q_n;H_{N-n}.
\]

Substitution into the recurrence proves the uniform formula. In particular,

\[
 h=0:\ J;S=-tcH_0,\qquad
 h=-1:\ J;S=-c(H_1+tq_1;H_0).
\]

The fake-bubble correction in the second identity is genuine. Replacing the
negative-weight initial value by a single monic cup loses it.

## Closed coefficient rows

Use the literal right closures `R` and `R₀` of `ElementaryClosure`, still
at `λ=μ−α_i`. Let `X,Y` be the left/right dots on `EE`, and `Z` the dot on
`E`. The normalized middle-bubble slides are

\[
 W_n(Y)=
 \begin{cases}
  \sum_{r=0}^{n}(r+1)Y^r;B_\lambda(Q_{n-r}),&\epsilon=0,\\
  \sum_{r=0}^{\lfloor n/2\rfloor}(2r+1)Y^{2r};B_\lambda(Q_{n-2r}),
       &\epsilon=1.
 \end{cases}
\]

Set `W_n=0` for `n<0`; `W₀=1`. These introduce only right-strand dots.
Since `q_n` and `H_m` have parities `εn` and `εm`,

\[
 R(e_a;q_n;H_m)=t^{(a+n)m}X^m;Y^a;W_n(Y).
\]

Hence

\[
\begin{aligned}
 R(K_{ab};S)&=-c\sum_{n=0}^{b-h}
 t^{b-h+1-n+(a+n)(b-h-n)}X^{b-h-n};Y^a;W_n(Y),\\
 R_0(K_{ab};e_s)&=cZ^a;W_{b+s-h+1}(Z).
\end{aligned}
\]

The highest left-dot term for `b≥h` is exactly

\[
 -c\,t^{b-h+1+a(b-h)}X^{b-h};Y^a.
\]

For the through family, put `χ(b)=b(b−1)/2`. The two-parity relations are
`X;τ=t τ;Y+1`, `Y;τ=t τ;X−t`, and `YX=t XY`. They give

\[
\begin{aligned}
 R(T_{ab};S)
 &=t^{b+\chi(b)}Y^a;\tau;Y^b\\
 &=t^{a+b+\chi(b)}\tau;X^a;Y^b
   -\sum_{j<a}t^{b+\chi(b)+j+1+j(a-1-j)}X^j;Y^{a+b-1-j},\\
 R_0(T_{ab};e_s)&=t^{bs+\chi(b)}Z^{a+b+s}.
\end{aligned}
\]

### Source coefficients in this target-side calculation

Let `θ_i(p)=(-1)^(ε|p|)p` on homogeneous coefficients and extend linearly.
Use the dot-first, coefficient-last transport `ρ⁺` from `ElementaryClosure`,
not the reversed-`End` serializer. Moving the original source prefix past
the entire component gives the following coefficient arguments:

| Component | Argument of the right-strand transport `ρ⁺` |
|---|---|
| `R(P_A(p);T_ab;S)` | `θ_i^(a+b+1)(p)` |
| `R(P_A(p);K_ab;S)` | `θ_i^(a+b+h)(p)` |
| `R₀(P_A(p);T_ab;e_s)` | `θ_i^(a+b+s)(p)` |
| `R₀(P_A(p);K_ab;e_s)` | `θ_i^(a+b+h+1+s)(p)` |

The transport adds no `X` dots. Every full-SYM coefficient has constant dot
coefficient `p`, including all ordered exterior products.

## Conditional elimination for the fixed family

Assume upward SKM independence over full SYM for `E1_λ` and `EE1_λ`.
First the `τ` rows and least-dot detection kill every through coefficient.
Then choose the greatest remaining cup index `b=B` with `B≥h`. Its left-dot
row `B−h` receives only `n=0` from that index; all other terms have a smaller
left-dot exponent. Its coefficient is a unit times a right-strand least-dot
transport. This kills the row; descend through `B`.

If `h≤0`, all cup labels have been killed. If `h>0`, only `0≤b<h` remain.
For the greatest remaining `B`, take `s=h−1−B`. The identity component has
bubble index `b+s−h+1=b−B`, so it vanishes below `B` and is the unit `c` at
`B`. The parity exponent there is `a+B+h+1+s=a+2h`, giving `θ_i^a`.
Least-dot detection kills this row too. Descending through `B` proves the
conditional fixed-family independence. No coefficient-domain assumption is
used.

## Source sorting has the opposite threshold

The preceding calculation is for **target** `EF`, by postcomposition. It
cannot be reused unchanged for **source** `FE`, by precomposition.
The actual component conventions are:

| Side being sorted | Components | Identity remainder |
|---|---|---|
| Target `EF` | `f;S`, `f;e_s` | `0≤s<h` |
| Source `FE` | `S;f`, `H_s;f` | `0≤s<−h` |

A minimal witness occurs at `h=−1`. The zero-dot left cap is
`ε'=c⁻¹ dcap₀`, and the actual relations give

\[
 S;\epsilon'=0,\qquad H_0;\epsilon'=c^{-1}\operatorname{id}.
\]

It is the cap matching `[.cap 0]` on source `[dn i,up i]`, with no crossings
and a single critical point; its zero-dot evaluation is the normalized
`epsP`. Under upward independence over nonzero SYM, this cap cannot vanish.
Thus the missing source identity component cannot be repaired by changing a
point, serializer, representative, or sign.

[`SortingDirection.lean`](../../scripts/NonVacuity/SortingDirection.lean)
checks these two identities, the normalized cap identification, and the
positive-weight target counterpart. Its concrete odd rational examples
discharge the datum, scalar and weight hypotheses. It does not assert
unconditional nonvanishing of the identity or formalize a full
`MatchingBasisChoice` witness.

With a right whisker `Q`, the parameter is the **local** weight
`h_i(wt D μ Q)`, not automatically `h_i(μ)`. The prospective source/cap shift
is `b+h`, with remainder `b<−h`; its complete signed coefficient comparison
is a separate calculation, not a consequence of the target formula above.

## Remaining contextual obligations and checks

To pass from these fixed families to arbitrary boundaries, one still needs
adapted strict representatives and explicit coefficient maps for both sorts.
The pivot variable is a **strand**, not a horizontal position. Absence of
pivot dots must survive residual matching normalization. One also needs a
finite signed-unit triangular change of representatives, points and
serializers, and a coefficient-level right closure of the sorted boundaries.
The existing spanning theorem and Hom-level bending identities do not supply
these assertions automatically.

Run `python3 scripts/Nondegeneracy/all_weight_elementary.py`. It checks the
cup recurrence initialized by the actual negative fake-bubble branch for
both parities, `h=-7,…,7`, and `b=0,…,11`; the both-parity through PBW
formula; finite remainder pivots; and sign/fake-bubble mutations. These are
exact formal integer-coefficient checks, not an SKM action or a global
independence proof. The all-weight derivation above is mathematical prose;
only the direction-witness identities in this addition are Lean-checked.
