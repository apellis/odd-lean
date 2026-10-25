# Source sorting and the boundary induction

**Mathematical result.** There is an injective formal coefficient comparison
for source sorting in mutually adapted strict matching families, over the
full abstract `SYM`. This construction uses residual spanning, not upward
independence. It is not yet a compiled Lean theorem.

Together with [target sorting](ContextualSorting.md) and the conditional
[sorted closure](SortedClosure.md), it reduces oriented independence to
upward SKM independence and an invertible arbitrary-choice comparison.
The arbitrary-choice comparison is now proved natively by
`MatchingBasisChoice.expansion_injective_choice_iff`; see
[MatchingChoiceTransition](MatchingChoiceTransition.md). The contextual local
family comparisons in this note still require their full native assembly.

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

The arbitrary-choice equivalences are now native theorems. Conditional on
full upward SKM independence over `SYM`, the mathematical construction gives
the oriented reduction together with [SortedClosure](SortedClosure.md). The
whole reduction is not yet formalized: the contextual coefficient comparisons
must still be assembled from actual families and inversion components.


## Compiled boundary induction and exact remaining interface

`ContextualBoundaryInduction.lean` proves the adjacent-inversion decomposition,
the exact one-step decrease, and the global nested induction on total boundary
length then inversion sum. Source and target contexts and colors are arbitrary;
its deletion premise is demanded only when the two colors are equal.

`ContextualNondegeneracy.lean` specializes this to the actual conjecture.
`BoundaryIndependence cs μ a b` quantifies every matching choice and requires
exactly the equal-weight boundary condition in `NondegeneracyConjecture`.
`nondegeneracy_of_contextual_descent` takes sorted independence plus explicit
`SourceExchangeDescent` and `TargetExchangeDescent` hypotheses. Every component
uses the unchanged global external `μ`; no local unwhiskered coefficient
formula is substituted for residual spanning. Actual weight preservation
under arbitrary-color swaps and same-color deletion is separately checked.

These local descent hypotheses are not disguised conclusions: they are the
precise still-open assembly of the adapted-family bijections, native inversion
identities, residual coefficient lifts, and finite paired-sector detector.
The generic induction does not claim to discharge them. Its concrete consumer
constructs a finite reduction tree for alternating boundaries with distinct
and repeated colors; a second consumer checks the conditional conjecture
assembly on the two-odd-color datum.

### Native frozen-prefix transport

`SourceFrozenSwap.step`, `fits`, and `run` prove that swapping two adjacent
frozen source endpoints commutes with every later valid matching move and with
the whole finite matching word. This includes actual cap ID renaming and the
complete crossing history. The checked consumer includes a cap which renames
an ID appearing in the frozen prefix, followed by a cup and crossing. This is
a source-attachment primitive, not yet the complete adapted source family.

`SourceFrozenSwap.ren` and `crit` additionally preserve the actual strand-ID
renaming and critical-ID lists. `SourceIdRelabel` proves validity, complete
state transport, critical-ID transport, and distinguished-point ID transport
for an injective relabelling fixing every fresh ID. Its `reducedData_iff`
preserves the full reducedness data. The concrete consumer uses an actual cap
and a permutation moving ID zero; no `f 0 = 0` premise is assumed. ID lookup
identities are restricted to valid active positions.

`SourceCrossState.start_cross` and `cross_run` now identify the actual initial-crossing state and its cap-renamed crossing history. `SourceCrossAttachment` constructs strict pointed attachments and low/high partners with actual count equivalences and literal initial-crossing serializers. `SourceCapAttachment` inserts the frozen cap pair and shifts fresh IDs by four, preserving the residual serializer and all added cap counts.

`SourceCompletedChoice` and `SourceAdaptedChoices` assemble complete same-colour choices: `exists_source_same_colour_adapted_equiv` retains every paired exponent and residual label, using `PointedMatching.ofStrict` on `B.members`. `SourceAdaptedDistinctChoices` proves complete distinct-colour choices without independence assumptions. `SameColourSourceFrame` attaches the native source coefficient columns with their full-SYM twists. `kernel_supported_paired` eliminates unpaired coefficients, while `PairedSourceDetection` and `PairedSourceIndependence` detect the paired sector at every height, including negative-height low-cup outputs and the odd-bubble correction in downward-dot normalization. `source_exchange_descent` proves the complete source interface. Together with `target_exchange_descent` and `WeakMate.sorted_independence`, this yields `nondegeneracy_of_upward_independence` and completes the upward-to-oriented reduction. Upward independence itself remains an explicit hypothesis.
