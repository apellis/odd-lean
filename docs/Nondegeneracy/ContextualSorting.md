# Contextual sorting with an isolated pivot strand

**Local result.** For a same-colour target swap `P EF Q → P FE Q`, there
exist mutually adapted complete unique strict matching families and an
injective map of their formal SYM coefficient modules intertwining the
actual sorting components. This statement uses residual spanning, **not
upward independence or injectivity of any matching evaluation**.

This is a mathematical construction, not a compiled SKM theorem. The
[source comparison and boundary induction](SourceContextualSorting.md) and
[conditional sorted closure](SortedClosure.md) are separate prose arguments.
The arbitrary-choice injectivity equivalence is now a native theorem.
Full upward SKM independence and the complete contextual local comparison
assembly remain open.

Throughout, composition is chronological. Put

\[
 A=P EF Q,\quad B=P FE Q,\quad C=PQ,\quad
 \nu=\operatorname{wt}(D,\mu,Q),\quad
 h=h_i(\nu),\quad t=(-1)^{|i|},\quad c=c_{\nu;i}.
\]

A bar denotes whiskering by `P,Q`, at global external weight `μ`. The
whiskers in these composites are identities, so placement preserves their
order without an interchange sign. Write `K=SYM D k` and `P_a(p)` for the
actual source placement of `β_μ(p)` on a source word `a`.

## 1. Mutually adapted families

Fix one complete unique strict residual family `G` from `a` to `C`, with
its points and serializer. Denote its decorated diagrams by `g_r`; the index
`r` includes the residual strand-dot counts.

For output endpoints paired to one another, choose

\[
 g_r;\overline J;\overline u^{\,b}\quad\text{on }A,
 \qquad g_r;\overline H_m\quad\text{on }B.
\]

Here `J` is the ordinary normalized left cup and `H_m` the right cup with
`m` dots on its upward leg. Append the undecorated cup after the residual
representative. Use the residual serializer before the cup and place the
new strand's dots after it. The cup adds no crossing and has just one
critical point; its strand is disjoint from every residual strand. Deleting
its adjacent boundary pair is the inverse bijection on pairing classes.

For distinct selected endpoints, swapping those endpoints toggles the
interleaving of their strands and preserves all other pairwise interleavings.
Choose a strict representative `g` on the noninterleaving side, and append
the single mutual crossing to obtain the other representative. Put all
distinguished points and decorated moves on `g`, before that crossing,
with the same serializer on both sides. The two selected strands had not
crossed; the new crossing changes no other intersection and adds no critical
point.

The crossing/interleaving assertion is the content of
`Chord.mem_xs_iff` in `SpanStrictReduced.lean`. The constructions
`realized_cup` and `realized_cross` explicitly preserve the crossing and
critical-point invariants. Together with `exists_strictReduced_matching`,
these give the required representatives class by class. Each paired class
and each distinct class occurs once; the residual family in both paired
sectors is the *same* `G`.

Reindex dot counts by the strand pair, not by an unchanged numerical
left-end label. If `τ` transposes the selected boundary positions, send the
pair `{j,k}` to `{τ(j),τ(k)}` and index it by `min(τ(j),τ(k))`. Bottom positions
in the bent boundary `a* B` remain fixed. For paired deletion, remove the two
positions, order-preservingly relabel all remaining positions, and restrict
the counts; retain the deleted strand's count as the separate index `b`.
These operations have inverse insertion maps.

## 2. Expand the residual morphism before appending the cup

For any `v:a→C`, residual spanning gives finite coefficients `d_r∈K` with

\[
 v=\sum_r P_a(d_r);g_r.
\]

Postcompose this equality with `\overline H_m`, **without normalizing that
terminal cup**:

\[
 v;\overline H_m=\sum_r P_a(d_r);g_r;\overline H_m.
\]

Every output term retains exactly `m` dots on the isolated cup strand.
Residual normalization can change other pairings, crossings, cups, caps and
dot counts, but cannot change a strand appended only afterwards.

In particular take `v=g_r;\overline{q_n}`, with the normalized loops of
[AllWeightSorting](AllWeightSorting.md). The bubble in the gap between `P,Q`
is simply an endomorphism of `C`. **Do not first slide it across `Q`.**
Expand this residual morphism directly by `MatchingBasisChoice.expansion_surjective`
for `(a,C)`, never by spanning for the entire `(a,B)` morphism.

For `n=0`, select the exact lift `g_r ↦ [r;1]`; for a zero loop select zero.
For every other fixed pair `(r,n)`, select any finite residual expansion.
There is no requirement for a linear section of the spanning surjection.

The extension to arbitrary source coefficients is well-defined and linear:

\[
 P_a(p);P_a(d);g=P_a(dp);g.
\]

The order is `d p`, not `p d`: `betaSYM` is an algebra homomorphism into
Lean's reversed `End` multiplication, as in `rightAction_mul`. Extend each
chosen finite column by left multiplication of its entries on the input
coefficient. This respects the right `K` action, including all exterior
products and zero divisors. No coefficient is commuted across a diagram,
so neither a parity involution nor changed-weight transport occurs here.

## 3. The principal and remainder columns

The formal comparison has target

\[
 C_{F'}(a,B)\ \oplus\ \bigoplus_{0\leq s<h} C_G(a,C),
\]

and intertwines evaluation with
`f ↦ (f;\overline S,(f;\overline e_s)_s)`. The tuple is empty for `h≤0`.

### Distinct endpoints

If the old representative is on the noninterleaving side, its new partner
is exactly `g;\overline S`: the distinct column has coefficient `+1`.
If the old side is interleaving, it is `g;\overline L`, and `eq_2_12_b` gives

\[
 g;\overline L;\overline S
 =-g+\sum_{0\leq j<-h}(g;\overline{\operatorname{dcap}_j});\overline H_j.
\]

Expand only each parenthesized residual morphism. Every correction lies in
the paired sector, and the distinct column has coefficient `−1`. All dots
were already before the final crossing; there is no mixed-dot straightening
or extra dot-order sign in this comparison. The distinct-sector projection
is therefore a signed bijection of labels. Remainder components of these
columns may be expanded arbitrarily by residual spanning.

### Paired endpoints

The actual all-weight identity gives

\[
 (g_r;\overline J;\overline u^{\,b});\overline S
 =-c\sum_{n=0}^{b-h}t^{b-h+1-n}
      (g_r;\overline{q_n});\overline H_{b-h-n}.
\]

Using the chosen residual lifts, the `n=0` coefficient column is precisely

\[
 -c\,t^{b-h+1}[r,b-h;p]\qquad(b\geq h).
\]

Every `n>0` term has strictly smaller pivot count `b-h-n`. Residual expansion
cannot change that count. Paired input columns never enter the distinct
output sector. The diagonal is an even scalar unit; in particular it has
no closed-formula parity twist from `ElementaryClosure`, since no closure
or coefficient reordering has occurred.

For `h>0` and `0≤s<h`, the identity component is

\[
 (g_r;\overline J;\overline u^{\,b});\overline e_s
   =c(g_r;\overline{q_{b+s-h+1}}).
\]

It is zero at negative bubble index and exactly `c[r;p]` at index zero.

## 4. Formal injectivity

All columns are finite, so they define a map on finitely supported
coefficient families. Suppose its output is zero **formally**.

1. The principal distinct projection kills every distinct input coefficient
   by its signed-bijection diagonal.
2. Among paired inputs, take the greatest occupied `b=B≥max(h,0)`.
   Output pivot `B-h` receives only `n=0` from that row. Its residual labels
   remain exactly `r`, and its coefficient is the unit
   `−c t^(B-h+1)` times the input. Thus the whole row vanishes. Descend through
   the finite support.
3. If `h≤0`, no inputs remain. If `h>0`, take the greatest remaining `B<h`
   and the identity component `s=h-1-B`. Smaller rows have negative bubble
   index and vanish; row `B` has diagonal `c`. Descend again.

This proves formal injectivity without any evaluation-injectivity input.
`LeastDotTransport.eq_zero_of_upper_coefficients` in
[`LeastDotTransport.lean`](../../scripts/NonVacuity/LeastDotTransport.lean)
checks the abstract greatest-occupied-row argument, allowing an arbitrary
additive coefficient object, including a residual-label module. Its concrete
matrix application discharges the triangular and diagonal hypotheses.
The SKM representative construction and intertwining map above remain prose.

If the adapted output evaluation maps are independently injective, this
formal map then proves injectivity of the old evaluation. It does not supply
that independent hypothesis.

## 5. Source-side caps: direct formulas and ordered coefficients

For the source calculation suppress whiskers and put `A=EF`, `B=FE`,
`C=epsP:B→1_μ`, `x=uRM`, with `h=h_i(μ)` and the same chronological notation.
Use the *clockwise* normalized family

\[
 \bar q_n=c\,\operatorname{bubRs}(i,\mu,n),\quad
 \bar q_0=1,\quad \bar q_n=0\ (n<0).
\]

Its explicit full-SYM lifts are complete-symmetric rather than elementary.
Let `h_r(i)` be the complete symmetric polynomial in the commuting
polynomial generators of colour `i`. Then

\[
 \bar Q_n=(-1)^n h_n(i)\quad(|i|=0),\qquad
 \bar Q_{2r}=(-1)^r h_r(i),\quad
 \bar Q_{2r+1}=(-1)^r\delta_i h_r(i)\quad(|i|=1).
\]

The evaluations follow from `beta_h`, `betaD_h`, `betaD_dh` and the
`betaSYM` generator comparisons; no faithfulness is needed.
The exact source formulas are

\[
\begin{aligned}
 H_r;C&=c^{-1}\bar q_{r+h+1},\\
 S;x^b;C&=c^{-1}\sum_{n=0}^{b+h}
       t^{b+h-n}e_{b+h-n};\bar q_n,\\
 H_s;x^b;C&=c^{-1}\bar q_{s+b+h+1}.
\end{aligned}
\]

The sum is empty for `b+h<0`; its principal coefficient is
**`+c⁻¹ t^(b+h)`**. Derive it from
`F_(b+1)=t u;F_b+c⁻¹ e₀;\bar q_(b+h+1)` using `sg_uR` and `uL_eL`.
For `h<0`, `F₀=0`. For `h≥0`, the actual definition
`C=−t^h c⁻¹ L;e_h`, the inversion block, and the negative branch of `bubR`
give

\[
 D_j;e_h=-t^{h-j}\bar q_{h-j}\quad(0\leq j<h),\qquad
 F_0=c^{-1}\sum_{n=0}^{h}t^{h-n}e_{h-n};\bar q_n.
\]

Both minus signs in the fake-bubble correction cancel. This is a direct
calculation, not an assumed reflection or pivotal symmetry.

Let `θ_i` be the parity involution with exponent `|i|`. Source precomposition
has **same-weight** coefficient transport:

\[
 S;P_{FE}(p)=P_{EF}(\theta_i p);S,\qquad
 H_s;P_{FE}(p)=\beta_\mu(\theta_i^s p);H_s.
\]

For a residual morphism `R:1_μ→Z`, put
`f_b=P_FE(p);x^b;C;R` and `k=b+h+1`. Moving the coefficient only across
`x^b;C` yields

\[
\begin{aligned}
 S;f_b&=c^{-1}\sum_{n=0}^{b+h}t^{b+h-n}
 e_{b+h-n};\bar q_n;\beta_\mu(\theta_i^k p);R,\\
 H_s;f_b&=c^{-1}\bar q_{s+b+h+1};\beta_\mu(\theta_i^k p);R.
\end{aligned}
\]

The consecutive bubbles combine as
`\bar q_n;β_μ(θ_i^k p)=β_μ((θ_i^k p)\bar Q_n)`, in that order.
There is no changed-weight `ρ` in these local source identities.

After principal elimination, the source remainder exists only for `h<0`.
For greatest remaining `B<−h`, choose `s=−h−1−B`: lower rows vanish and the
pivot is `c⁻¹` with invertible coefficient twist `θ_i^s`, without another
scalar sign.

For a representative already factored as an isolated bottom cap followed
by a residual matching, normalize only the suffix after the cap. All
correction bubbles and transported coefficients occur there; the terminated
pivot strand cannot acquire more dots. With context `P,Q`, use local
`h_i(wt D μ Q)` while the source coefficient retains global weight `μ`.
These cap formulas alone are not the complete source comparison. Its
distinct sector, ordered coefficient columns and formal injectivity are
derived in [SourceContextualSorting](SourceContextualSorting.md).

## Verification and remaining work

`python3 scripts/Nondegeneracy/source_cap_sorting.py` checks the source
recurrence, ordered coefficient parities and finite remainder entries.
These are finite exact checks, not an SKM action or a proof of faithfulness.
The new greatest-pivot lemma and its concrete application are Lean-checked;
the contextual matching construction is not yet formalized.

Still needed for the full conjecture: arbitrary-choice invertible comparison,
full upward SKM independence, and formalization of the contextual sorting and
sorted-closure arguments. The [crossing-filtered expansion](MatchingChoiceTransition.md)
is Lean-proved, but does not supply the lower-dot comparison or the inverse.
Hom reconstruction
identities alone do not close any of those coefficient-level obligations.

## Native distinct-color crossing action

`DistinctContextualCrossing.lean` now proves the actual contextual sigma and
left-crossing morphisms are mutual inverses for distinct colors, with arbitrary
left/right contexts and the correct local weight `wt μ Q`. It constructs both
source and target Hom linear equivalences at global external weight `μ`.
Target exchange preserves every ordered source coefficient exactly. Source
exchange applies the full-SYM parity involution for `|i||j|`; no `t_ij` factor
or homogeneous-coefficient restriction is introduced. Its concrete consumer
uses nonempty contexts, two odd colors, and an inhomogeneous exterior-product
coefficient.

This does not by itself establish basis independence under the exchange: an
isomorphism of Hom spaces is not yet a verified matching-basis correspondence.
The remaining native step is to assemble the adapted complete matching
families, their dot serializers, and the exact label-level crossing identity.

`DistinctExchangeIndependence.lean` additionally checks the actual decorated
low-side insertion and high-side cancellation identities for both source and
target exchange. They retain arbitrary decorated prefix/suffix layers and
have exact leading coefficient `+1`. Given the adapted label bijection and
its literal serializer correspondence, the native
`distinct_target_adapted_independent` and
`distinct_source_adapted_independent` transfer full-SYM independence. The
source proof uses target coefficient placement temporarily and the proved
parity involution to return to the library convention. Their family
correspondence premise is still explicit until the complete adapted-choice
bundle is assembled; it is not an assumption of evaluation independence.

### Distinct-colour target descent is native

`DistinctTargetDescent.distinct_target_exchange_descent` (in namespace
`OddMath.SKM`) now discharges the distinct-colour target branch itself. For
arbitrary contexts, external weight, and source, independence for the swapped
target implies independence for the original target when the colours differ.
The theorem constructs the complete adapted families and their label bijection,
uses actual terminal-crossing insertion or cancellation on each class, and
transfers the resulting independence to every matching choice. All coefficients
belong to full `SYM`; no adapted-family or homogeneous-coefficient premise is
left. The source distinct-colour branch and the equal-colour paired-sector
assembly remain separate obligations.
