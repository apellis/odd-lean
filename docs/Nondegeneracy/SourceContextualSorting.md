# Source sorting and the boundary induction

**Mathematical result.** There is an injective formal coefficient comparison
for source sorting in mutually adapted strict matching families, over the
full abstract `SYM`. This construction uses residual spanning, not upward
independence. It is not yet a compiled Lean theorem.

Together with [target sorting](ContextualSorting.md) and the conditional
[sorted closure](SortedClosure.md), it reduces oriented independence to
upward SKM independence and an invertible arbitrary-choice comparison.
The latter comparison is not yet established: only its crossing-filtered
expansion input is currently proved in Lean; see
[MatchingChoiceTransition](MatchingChoiceTransition.md).

## Setup and adapted families

Use chronological composition. Fix an output word `Z` and put

\[
 B=P F_iE_iQ,\quad A=P E_iF_iQ,\quad C=PQ,\quad
 \nu=\operatorname{wt}(D,\mu,Q),\quad h=h_i(\nu),\quad
 t=(-1)^{|i|},\quad c=c_{\nu;i}.
\]

Every local morphism below is whiskered by the identity words `P,Q`.
The global source coefficient placement is `P_W(p)` at external weight
`μ`, not `ν`. Write `K=SYM D k`, let `Θ` be its parity involution, and put
`θ=Θ^{|i|}`. These involutions act on arbitrary, possibly inhomogeneous
coefficients and retain all products of exterior generators.

Choose one complete unique residual family `g_r:C→Z`, with `r` including
its strand-dot counts. For paired selected endpoints choose

\[
 T_b;g_r\quad\text{on }B,\qquad e_m;g_r\quad\text{on }A,
 \qquad T_b=x^b;\epsilon',\quad x=u_{RM}.
\]

The initial cap is isolated. Put its dots before the cap and all residual
dots afterwards, with the inherited serializer. Deleting that boundary
pair recovers the same residual class on both sides. For distinct selected
endpoints, choose a representative on the noninterleaving side and prepend
the crossing to get its partner, with all dots in the common suffix.
Endpoint transposition gives the pairing and strand-count bijections.
The added cap has one critical point; the added crossing is the unique
crossing of the two selected strands. Thus these are strict representatives.

Let `S:A→B` be the right mixed crossing, `L:B→A` its presentation partner,
and `H_s:C→B` the dotted right cup. Their source coefficient rules are

\[
 S;P_B(p)=P_A(\theta p);S,\quad
 H_s;P_B(p)=P_C(\theta^s p);H_s,\quad
 e_m;P_C(d)=P_A(\theta^m d);e_m.
\]

These follow from the parities of `sigmaL`, `etaL`, `epsL` and contextual
super-interchange. They involve no changed-weight bubble transport.

## Paired columns with ordered coefficients

Use the normalized clockwise loop `\bar q_n=c\operatorname{bubRs}(i,ν,n)`.
It has `\bar q_0=1` and vanishes at negative index. Choose finite residual
expansions at global weight `μ`:

\[
 \bar q_n;g_r=\sum_\ell P_C(d_{r,n,\ell});g_\ell.
\]

Prescribe the Kronecker identity lift at `n=0`, and zero lifts at `n<0`.
Other lifts need not be unique. In a nonempty context do not replace these
coefficients by the unwhiskered complete-symmetric formula without proving
the necessary bubble slides. Spanning of the residual Hom already suffices.

The all-weight cap identities derived in [ContextualSorting](ContextualSorting.md)
are

\[
 S;T_b=c^{-1}\sum_{n=0}^{b+h}t^{b+h-n}e_{b+h-n};\bar q_n,
 \qquad H_s;T_b=c^{-1}\bar q_{s+b+h+1}.
\]

The first sum is empty when `b+h<0`. The formal comparison has target

\[
 C_{F'}(A,Z)\oplus\bigoplus_{0\le s<-h}C_G(C,Z)
\]

and intertwines evaluation with `f↦(S;f,(H_s;f)_s)`. For input label `(r,b)`
and coefficient `p`, its principal column is

\[
 \sum_{n=0}^{b+h}\sum_\ell
 [\ell,m;\ c^{-1}t^m\theta^m(d_{r,n,\ell})\theta(p)],
 \qquad m=b+h-n.
\]

Its remainder column at `s` is

\[
 \sum_\ell[\ell;\ c^{-1}d_{r,s+b+h+1,\ell}\theta^s(p)].
\]

The order and the separate twist on `d` are essential. For example,

\[
 P_A(\theta p);e_m;P_C(d);g_\ell
 =P_A((\theta^m d)(\theta p));e_m;g_\ell.
\]

This uses `P(p);P(d)=P(dp)`, the source-placement convention inherited from
reversed `End` multiplication. No linear section of the spanning map is
assumed: choose each finite unit-input column once, then use these formulas.
The components are `k`-linear; their different parity twists mean the whole
map need not be right-`K`-linear with untwisted actions.

Expanding only the residual suffix cannot change the terminated cap strand.
At `n=0` the principal pivot is therefore exactly

\[
 [r,b+h;\ c^{-1}t^{b+h}\theta(p)]
 \qquad(b\ge\max(-h,0)),
\]

and all `n>0` corrections have smaller pivot count.

## Distinct-endpoint columns

If the old side is noninterleaving, the new representative is `S;g`, giving
`[u';θ(p)]`. If the old side is interleaving, it is `L;g` for a new
noninterleaving representative `g`. The relevant identity is
`eq_2_12_a` in `MoreGenerators.lean`:

\[
 S;L=-1_A+\sum_{0\le j<h}e_j;\operatorname{dcup}_j.
\]

Choose finite residual lifts
`dcup_j;g=∑_ℓ P_C(a_{u,j,ℓ});g_ℓ`. The principal column is

\[
 [u';-\theta(p)]
 +\sum_{0\le j<h}\sum_\ell
 [\ell,j;\ \theta^j(a_{u,j,\ell})\theta(p)].
\]

All corrections are paired; this sum is empty for `h≤0`. Choose arbitrary
finite lifts `H_s;old_u=∑_ℓP_C(v_{u,s,ℓ});g_ℓ`; the remainder column is
`∑_ℓ[ℓ;v_{u,s,ℓ}θ^s(p)]`. Thus the distinct principal projection is a
signed, parity-twisted bijection, unaffected by paired input columns.

For different colours use `A=P E_jF_iQ`, `B=P F_iE_jQ`, `i≠j`.
There is no paired selected-endpoint class. The literal identities
`sg_lc_ne` and `lc_sg_ne` in `LeftDot.lean` give `S;L=1` and `L;S=1`, with plus signs.
Both source cases have column `[u';Θ^{|i||j|}(p)]`, with no remainder or
extra `t_ij` scalar in these normalized conventions. The corresponding
target-side column is `[u';p]`, since it does not move a source coefficient
across the appended crossing.

## Formal injectivity

Every column and each remainder tuple are finite. If the formal output
vanishes, first use the distinct projection to kill all distinct inputs.
For paired inputs choose the greatest occupied row `B≥max(-h,0)`.
Output pivot `B+h` receives only the displayed `n=0` diagonal from that
row; smaller input rows cannot reach it. Its scalar is a unit and `θ` is
invertible, so the row vanishes. Descend through the finite support.

If `h≥0`, no rows remain. Otherwise choose the greatest remaining `B<−h`
and set `s=−h−1−B`. The remainder index is `b−B`, so smaller rows vanish
and row `B` has diagonal `c⁻¹θ^s`. Descend again. This proves formal
injectivity without cancelling exterior generators or assuming evaluation
independence.

## Termination and the exact conditional reduction

For boundary words `(a,z)` use lexicographic measure

\[
 \bigl(|a|+|z|,\ I_{FE}(a)+I_{EF}(z)\bigr),
\]

where `I_FE` counts a downward letter before an upward one, and `I_EF`
counts the reverse orientation. Source sorting `FE→EF` and target sorting
`EF→FE` decrease their respective inversion counts by one. A remainder
removes a **same-colour** opposite pair and decreases total length.
Every swap preserves weight; only same-colour pairs are deleted. Distinct
opposite-oriented colours need not have total weight zero.

Each node has finitely many components and each branch terminates at
source `UD`, target `D'U'`. Recompute the local `ν=wt D μ Q` at every edge.
The induction hypothesis should assert independence for **every choice** at
smaller boundaries. It then applies to whatever output families the local
map requires. An independently established invertible choice transition
transfers the adapted input result to an arbitrary input family. No single
globally compatible collection of representatives is required.

Keep three arguments separate: boundary induction uses this measure;
choice transitions lower `(crossings, open-strand dots)`; sorted closure
uses greatest crossing length followed by least occupied dot degree.
Increasing dots in closure transport do not give a terminating inverse
rewrite.

Conditional on the missing arbitrary-choice equivalences and full upward
SKM independence over `SYM`, this gives the oriented reduction together
with [SortedClosure](SortedClosure.md). The whole reduction is not yet
formalized, and neither missing input is supplied by these local formulas.
