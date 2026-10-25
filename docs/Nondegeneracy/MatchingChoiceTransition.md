# Crossing-filtered expansions and matching choices

Choice independence is proved in Lean. For any two complete decorated matching
choices `F,G` on the same boundary, `expansion_injective_choice_iff` proves

\[
\operatorname{Injective}(\operatorname{expansion}_F)
\iff \operatorname{Injective}(\operatorname{expansion}_G).
\]

The native implementation is
[`MatchingChoiceTransition.lean`](../../OddMath/SKM/MatchingChoiceTransition.lean),
using finite right-coefficient bookkeeping in
[`MatchingChoiceCoefficients.lean`](../../OddMath/SKM/MatchingChoiceCoefficients.lean).
It constructs a signed triangular transition and proves its evaluation identity
and injectivity. This establishes independence of choices; it does not establish
injectivity for even one choice or prove upward SKM independence.

## Crossing-filtered expansions

For any `MatchingBasisChoice F`, external weight `μ`, and natural ceiling `N`,

\[
 f\in\mathrm{LtL}(N)\quad\Longrightarrow\quad
 \exists z,\quad \operatorname{expansion}_F(z)=f,\qquad
 \operatorname{supp}(z)\subseteq
 \{t:\operatorname{crossings}(t)<N\}.
\]

This is `MatchingBasisChoice.exists_expansion_of_mem_ltL` in
[`Nondegeneracy.lean`](../../OddMath/SKM/Nondegeneracy.lean). The vector `z`
is finitely supported and its coefficients belong to the abstract `SYM`,
not just the image of `betaSYM`. Its coefficients use the same source
placement as `MatchingBasisChoice.expansion`. There is no dot bound when
the crossing count drops, and no assertion that `z` is unique.

The proof retains information from the existing normalization:

1. `ltL_le_of_canon_dots_mem` in
   [`SpanMatchings.lean`](../../OddMath/SKM/SpanMatchings.lean) runs the
   crossing induction only below `N`. Cap elimination and chord
   normalization preserve that ceiling.
2. The canonical decorated step now needs the chosen family only at the
   current crossing count `c`. Its hypothesis is restricted by
   `ncr₂ R = c`, rather than requiring all representatives to lie in the
   submodule. Completeness of the family is unchanged; the family itself
   is **not** truncated before invoking completeness.
3. `ltL_le_diagBubSpan_decoratedFamily₂` in
   [`SpanDecoratedMatchings.lean`](../../OddMath/SKM/SpanDecoratedMatchings.lean)
   bounds the crossing count of every chosen representative after bending
   back. The existing unfiltered spanning theorem is a consequence.
4. `bubble_swap` and `betaSYM_range` move each rightmost coefficient to the
   source and lift it to `SYM`, without changing its matching label. The
   image of the submodule of coefficient vectors supported below `N`
   contains every such diagram.

These statements retain the existing datum, scalar and ground-ring
hypotheses. They do not require a field, a domain, finitely many colours,
upward independence or faithfulness of `betaSYM`.

[`MatchingCrossingFiltration.lean`](../../scripts/NonVacuity/MatchingCrossingFiltration.lean)
applies the result to dotted two-colour odd matchings over admissible
rational scalar data: a one-crossing matching expands using fewer than two
crossings, and a zero-crossing matching expands using only zero-crossing
representatives. These examples do not assert that their evaluated
morphisms are nonzero.

## Signed decorated comparison

`canon_dots_signRel_decorated₂` in
[`SpanDecoratedMatchings.lean`](../../OddMath/SKM/SpanDecoratedMatchings.lean)
retains the leading sign from the canonical normalization. Given a reduced
matching `R` with pairing isomorphic to `s`, any valid distinguished points and
serializer, and a list `is` of open dot positions, it gives

\[
 \operatorname{canonDots}(s,\mathrm{is})
 =(-1)^p\operatorname{bentDecorated}(R,n)+e_C+e_F+e_D,
 \qquad n(j)=\#\{i\in\mathrm{is}:\operatorname{lEnd}_s(i)=j\}.
\]

Here `e_C` has strictly fewer crossings; `e_F` lies in `FewerDots` on the
canonical skeleton; and `e_D` lies in `DecSpan` on the chosen bent skeleton.
Both latter submodules have strictly fewer than `is.length` open dots, with
unrestricted bubble products. `canon_dots_eq_sign_decorated₂_add_errors`
extracts these three errors separately. No complete family, ambient spanning
hypothesis, or coefficient-faithfulness assumption enters either statement.

The existing `canon_dots_mem_step` now consumes this comparison, with its
statement unchanged. The errors remain morphisms, not finite abstract-SYM
coefficient vectors. The importing examples in
[`MatchingDecoratedSign.lean`](../../scripts/NonVacuity/MatchingDecoratedSign.lean)
use a two-colour odd matching over rational scalars: three dots including a
repeated dot, and a zero-dot comparison in which both lower-dot errors vanish.

## The signed choice comparison

For complete unique choices `F,G`, identify their matching classes by the
endpoint pairing, and transport strand counts with
`matchingStrandEquivOfIso` in `DecoratedNormalization.lean`. The checked statement is

\[
 \operatorname{ev}_F(t)
 =\epsilon_t\operatorname{ev}_G(e(t))
   +\operatorname{expansion}_G(r_t),\qquad \epsilon_t\in\{1,-1\},
\]

where `r_t` has finite support strictly below

\[
 (\operatorname{crossings}(t),\operatorname{openStrandDots}(t))
\]

in lexicographic order. The second coordinate counts dots on open matching
strands, not dots used to draw bubbles and not the weighted degree.

Several needed relations already preserve a leading sign:

- `reduced₂_bent_normal_form` and `reduced₂_normal_form` compare arbitrary
  reduced skeletons with their canonical pairing diagram modulo fewer
  crossings.
- `DotBase.dots_up` and `dots_to_lEnd` preserve the leading strand counts;
  their errors have fewer crossings or fewer open-strand dots.
- `canon_dots_signRel_decorated₂` retains the chain of `SignRel` witnesses
  underlying `canon_dots_mem_step`. Converting its two lower-dot errors into
  coefficient vectors requires the lower-dot induction, not unrestricted
  surjectivity.

The sign assertions concern the repository's normalized layer evaluations.
They do not say that every raw cyclicity relation has coefficient `±1`.
Normalized odd-bubble slides are important: the same-crossing dot-turn
error loses a strand dot and its odd bubble slides without regenerating
strand dots. General bubble slides need not have that property.

The crossing-filtered result above handles the lower-crossing errors.
The filtered normalization below handles lower-dot sectors on arbitrary reduced
skeletons; the signed comparison between two families is checked in the native library.

## Filtered lower-dot normalization

The native choice-transition module defines `MatchingBasisChoice.openDots` as the finite sum of the actual strand
multiplicities, and `dotBound c N` by

\[
 \operatorname{crossings}(t)<c\quad\text{or}\quad
 \bigl(\operatorname{crossings}(t)=c\ \text{and}
       \operatorname{openDots}(t)<N\bigr).
\]

`strand_count_sum` identifies the canonical list length with that strand sum.
The bounded canonical step retains the corresponding restriction on its family
premise; simultaneous induction then normalizes the canonical and decorated
lower-dot sectors without truncating the complete family.

`MatchingBasisChoice.bounded_errors_mem` places those sectors in the `bendG`
preimage of the expansion image of coefficient vectors supported on `dotBound`.
Membership in this image supplies finite abstract-SYM coefficients. Source
placement uses `bubble_swap` and `betaSYM_range`, without assuming faithfulness.
There is no dot restriction when the crossing count drops.

The original decorated clause applies only to skeletons **in the chosen family**.
The new `bounded_arbitrary_errors_mem` strengthens it to every reduced matching
skeleton, including a representative from another family. Its proof is a second
induction on `n ≤ N`, keeping the target filtered image fixed. At the successor
step, apply `decSpan_le_step` with the set of all reduced matching skeletons.
Its canonical premise follows from the first clause of `bounded_errors_mem`,
because a list of length at most `n` has length strictly less than `N`. Its
recursive decorated premise is the induction hypothesis. This step needs no
completeness hypothesis on that auxiliary set and no additional independence
assumption. At `n = 0`, the decorated-error span is zero.

This removes the need for a simultaneous recursion between the two families:
both representatives' lower-dot errors normalize directly into the fixed target
family. The endpoint reindexing, canonical endpoint-dot list, and signed leading label
through bending are now constructed by `labelsEquiv`,
`exists_canonical_strand_dots`, and `labels_filtered_signRel`. These results are
part of the native module. Their printed axiom dependencies are exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## The checked coefficient transition

`columnData` chooses each unit leading sign and finite lower coefficient vector
once. `unitColumn` combines its signed leading single with that lower vector.
The generic `MatchingTransition.rightColumn` extends a column to coefficient
`p` by multiplying every entry `d` on the right: `d*p`, not `p*d`.
`MatchingTransition.transition` uses `Finsupp.lsum` to assemble those maps.
There is no arbitrary new preimage choice depending on `p`.

`choiceTransition_evaluation` proves the native evaluation identity

\[
\operatorname{expansion}_G(Tx)=\operatorname{expansion}_F(x).
\]

Its key compatibility lemma is `expansion_rightColumn`, proved from
`rightAction_mul`; it retains the repository's actual source placement and the
noncommutative coefficient multiplication order.

`choiceTransition_injective` uses greatest crossing count and then greatest open
dot count in finite support. At that complexity, strict-lowering entries vanish,
and the label equivalence separates distinct leading columns. Multiplication
by each leading sign reflects zero over an arbitrary ground ring. The generic
finite-support argument is `MatchingTransition.transition_injective`.

Consequently `expansion_injective_of_choice` transfers injectivity from `G` to
`F`; its symmetric use gives `expansion_injective_choice_iff`.

Surjectivity is also now checked. `MatchingTransition.transition_surjective`
works for arbitrary well-founded strict lower relations and right-invertible
leading coefficients. It constructs each target single recursively from its
source column and finitely many lower errors, with no uniform depth bound.
`choiceTransition_surjective` specializes it to crossing/open-dot order, and
`choiceLinearEquiv` bundles the resulting coefficient-space isomorphism. This
surjectivity result also allows weak-reduced families to be compared into a
strict family without first proving strictness of those source skeletons.

The audit script
[`MatchingDotFiltration.lean`](../../scripts/Nondegeneracy/MatchingDotFiltration.lean)
now imports the native module and prints the axiom dependencies of the principal
normalization, transition, and independence-transfer theorems.

## Construction of a unit column (checked)

Fix a label `t = (R,n)` of `F`. Completeness of `G` chooses a representative
`S` with the same endpoint pairing, and uniqueness makes this choice a bijection
of matching classes. The equivalence `matchingStrandEquivOfIso` preserves the
underlying left-endpoint number, so transports `n` to a multiplicity `n′` on `S`
and preserves its sum. Reducedness makes the two crossing counts equal; call the
common count `c`, and put `N = ∑ n(j)`.

Choose the common canonical pairing `s`. Form the finite list `is` by listing
each left endpoint `j` exactly `n(j)` times, in any fixed order. A left endpoint
is fixed by `lEnd s`, so `(is.map (lEnd s)).count j = n(j)`, and the list length
is `N`. All positions are valid. Apply `canon_dots_signRel_decorated₂` twice,
using the actual distinguished points and serializers of `F` and `G`. Writing
`B_F` and `B_G` for their bent decorated diagrams, this yields

\[
 C=\epsilon_F B_F+e_F,
 \qquad C=\epsilon_G B_G+e_G.
\]

Both errors lie in the fixed target submodule

\[
 T=\operatorname{bendG}^{-1}
 \left(\operatorname{expansion}_G
   (\text{coefficient vectors supported on }\operatorname{dotBound}(c,N))
 \right).
\]

Indeed, crossing errors use `exists_expansion_of_mem_ltL` and
`bendG_mem_ltL`; canonical lower-dot errors use `bounded_errors_mem`; decorated
lower-dot errors on **either** skeleton use `bounded_arbitrary_errors_mem`.
These are submodule inclusions, so arbitrary sums and signs are retained.
Subtracting the two equalities gives
`B_F = ε_F ε_G B_G + ε_F (e_G-e_F)`.

Apply the linear map `bendG`. By `bendG_bendF_xev`, each leading diagram
acquires a known sign depending on its parity. Both signs are units, so moving
the source sign to the other side leaves one unit leading sign and an error in
the target filtered image. Membership in that image supplies the required
finite abstract-SYM coefficient vector `r_t`. No faithfulness of the bubble map
or uniqueness of the error coefficients is used. This is checked as `labels_filtered_signRel` in the native module. The finite
coefficient witness is extracted by `exists_signed_column`; the construction
then proceeds through the checked coefficient transition described above.

## Weak inverse-mate realizations

`OddMath/SKM/WeakMatchingChoice.lean` now removes the strict critical-point
condition from the source of the comparison. A `WeakMatchingChoice F` supplies
one weakly reduced word for each class in the strict target `F`, with a pairing
isomorphism and actual distinguished points and serializers. Its
`filtered_signRel` and `unitColumn_eval` compare these literal diagrams with
`F`; `transition_surjective` and `transition_evaluation` prove the finite
abstract-SYM transition and its evaluation identity. Consequently
`strict_expansion_injective` transfers independence of that weak family to `F`.
This theorem does not assume strictness of the weak words, faithfulness of
bubbles, or independence of the strict target.

`OddMath/SKM/WeakMateMatchings.lean` combines source-prefix cups with target-suffix
caps on actual matching words. Weak reducedness and crossing count are
preserved. The composite strand equivalence transports every dot count
bijectively, preserves its sum, and transports bounded actual points and
serializers. `PairingRotation` and `WeakMateCoverage` now prove matching-class coverage and
reflection by cyclic endpoint rotation. `WeakMateChoice` assembles the actual
representative bijection, the complete weak choice, and the bijection of dot
labels. Its `weakChoice_layers` identifies the literal inverse-mate serializer.
The remaining sorted-boundary integration is its ordinary layer-list bridge
to `partialRightMateL` and the checked positive-dot closure coefficient
detector. These modules do not yet claim the full upward-to-oriented implication.

The normalization transition uses **decreasing** dots at fixed crossing count.
This is independent of the closure calculation on the weak family, whose
positive-dot corrections use **increasing** dots. The two triangular
arguments must be applied successively, not conflated into one order.

Both modules pass targeted warnings-as-errors builds. The concrete consumer
`scripts/NonVacuity/WeakMatchingChoice.lean` checks finite transition surjectivity
and evaluation on a nonempty odd boundary, and a literal combined cup/cap
example with all dot counts. Its printed axioms, including the independence
transfer theorem, are only `propext`, `Classical.choice`, and `Quot.sound`.
