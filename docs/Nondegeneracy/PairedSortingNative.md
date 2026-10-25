# Native paired-sector sorting identities

`OddMath/SKM/PairedSorting.lean` connects the full mixed inversion matrix
to the paired endpoint sector in the actual SKM presentation. It supplies
local identities for all weights and both colour parities. It does not
yet assemble contextual representative maps or prove arbitrary-boundary
independence.

Write `h=h_i(μ)`, `t=(-1)^|i|`, `c=c_(μ,i)`, `J=etaP`, `C=epsP`,
`S=sigma`, `u=uLM`, `x=uRM`, `e_s=eLM(s)`, and `H_s=hLM(s)`.
Composition below is chronological. The checked power identities are

`u^b;e_s=e_(b+s)`, and `H_s;x^b=H_(s+b)`.

Consequently the actual identity components have the unit pivots

`J;u^b;e_s = c δ_(b+s,h−1)` whenever `b+s<h`,

`H_s;x^b;C = c⁻¹ δ_(s+b,−h−1)` whenever `s+b<−h`.

These are `paired_target_low` and `paired_source_low`. They use the
degree-zero bubble identity, never cancellation of an exterior generator.

The principal components satisfy the checked recurrences

`J;u^(b+1);S = t (J;u^b;S;x − J;e_b;H_0)`,

`S;x^(b+1);C = t u;S;x^b;C + e_0;H_b;C`.

These are `paired_target_step` and `paired_source_step`. They are equalities
of actual source morphisms, with no coefficient-independence hypothesis.

The all-power versions are now checked too:

`J;u^b;S = t^b J;S;x^b + Σ_(s<b) (-t^(s+1)) J;e_(b−1−s);H_s`,

`S;x^b;C = t^b u^b;S;C + Σ_(s<b) t^s e_s;H_(b−1−s);C`.

These are `paired_target_expansion` and `paired_source_expansion`.
They retain the residual loops in their actual diagrammatic order.

The other two checked identities supply the initial rows when the
principal component does not vanish. For `h≤0`, set `N=−h` and
`α=zsign(ipar(i,μ))c`. Then

`J;S = α (Σ_(j<N) H_N;dcap_j;H_j − H_N)`.

For `h≥0`, set `M=h` and `β=−t^h c⁻¹`. Then

`S;C = β (Σ_(j<M) e_j;dcup_j;e_M − e_M)`.

The sums have strictly smaller terminal cup/cap index than their displayed
unit leading term. On the opposite height branches, the existing source
identities give `J;S=0` for `h>0`, and `S;C=0` for `h<0`.

## Why these are enough for the triangular proof

The leading/lower extraction is now itself kernel-checked, not only the
recurrence. The four theorems are:

| Side and height | Input dot count | Pivot index | Pivot coefficient |
| --- | --- | --- | --- |
| target, `h=N>0` | `N+m` | `m` | `-t^(m+1)c` |
| source, `h=-N<0` | `N+m` | `m` | `t^m c⁻¹` |
| target, `h=-N≤0` | `b` | `N+b` | `-t^b α` |
| source, `h=N≥0` | `b` | `b+N` | `-t^b β` |

They are `paired_target_leading_pos`, `paired_source_leading_neg`,
`paired_target_leading_nonpos`, and `paired_source_leading_nonneg`.
Each states an exact equality with finite lower-index sums. Separate
theorems prove all four displayed coefficients are units.
`paired_inverse_indices_lower` and `paired_slide_indices_lower` check
the two opposite-height lower-index bounds.

For target sorting with `h≤0`, iterate the first recurrence. The initial
leading cup `H_N` becomes `H_(N+b)` with unit coefficient, while initial
corrections remain lower and recurrence corrections have cup index at
most `b−1`. For `h>0`, the first nonzero loop in the recurrence occurs
at `b=h−1`; its coefficient is precisely `c`, giving the leading cup
`H_(b−h)` at input count `b≥h`. The source argument is dual, with
threshold `max(-h,0)`.

This argument does not require a closed formula for every fake bubble.
The lower loops can be expanded using residual spanning, with arbitrary
fixed finite lifts. Because they occur on the residual side of the
isolated cap or cup, they cannot change its pivot dot index. The native
recurrences therefore give exactly the local data needed by the
greatest-occupied-row proof in [ContextualSorting](ContextualSorting.md)
and [SourceContextualSorting](SourceContextualSorting.md).

## Residual coefficient lifting

`ResidualCoefficientLift.lean` now supplies actual finite abstract-`SYM`
lifts at the unchanged global weight `μ`. It chooses each positive-index
unit column once using `MatchingBasisChoice.expansion_surjective`, then
extends it by right coefficient multiplication. Negative-index columns
are prescribed as zero; the zero-index column is prescribed as the
original singleton with coefficient one. These prescriptions are made
by formal index, not by equality of evaluated morphisms, so no hidden
faithfulness assumption enters the choice.

`residualRow` embeds such a vector at an isolated-strand dot count, and
`residualRow_apply_ne` proves it contributes to no other dot row.
`postRowsExpansion_residualRow` evaluates target-side insertion as the
residual expansion followed by the actual cup. The source-side theorem
`preRowsExpansion_residualRow` inserts the cap's full-`SYM` parity twist
on the residual coefficients. `preRowsExpansion_twistedColumn` then
extends this column with the separately twisted original input
coefficient. It proves the ordered source formula rather than commuting
the two coefficients or assuming they are homogeneous.

The consumer uses a populated one-strand residual family, two distinct
odd colours, and an actual dotted cap in a nonempty context. Its
boundary chain is checked. Neither coefficient lift nor insertion uses
residual independence.

The remaining local work is to combine these finite columns with the
four leading/lower formulas, whisker the inversion matrix by contexts,
and identify the inserted decorated families with the actual adapted
matching choices. The global boundary induction and arbitrary-choice
transport are separate modules; these local lemmas do not by themselves
discharge their exchange hypotheses.

## Actual paired serializers and finite detection

`PairedCupEvaluation.lean` now identifies the literal serializers from
`PointedMatching.appendCup` with the native paired rows. With either
orientation, all new dots lie on the upward leg. The upward-first cup
therefore evaluates exactly as `J u^b`, and the downward-first cup as
`H_b`. The contextual formulas retain the original residual serializer
and place these local morphisms using `plcW` at weight `wt D μ Q`.
There is no change of the global coefficient weight `μ`. The consumer
uses a nonempty residual strand, two odd colours, and positive dot
counts on both the old strand and the appended cup.

`PairedCoefficientComparison.lean` proves injectivity of the finite
coefficient comparison once its rows have the established lower-dot
support and unit pivots. The output index may include both principal
and shortened-boundary families. Each component may apply its own
full-`SYM` parity twist; no common right-`SYM` linearity is assumed.
The proof selects a greatest occupied dot row and cancels only a unit,
then uses the parity involution. Its consumer includes a nontrivial
exterior lower correction and alternating parity twists. The native
`paired_target_below` and `paired_source_below` lemmas also establish
vanishing of the principal crossing below the relevant height cutoff.

The remaining assembly is the explicit finite column map joining
these actual paired families to the unpaired matching families and
proving its coefficient identities. The serializer and detector results
are infrastructure for this step, not a completed same-colour exchange
descent theorem.
