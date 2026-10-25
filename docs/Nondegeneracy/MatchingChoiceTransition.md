# Crossing-filtered expansions and matching choices

Crossing-filtered coefficient extraction and the unit-leading signed comparison
with explicitly bounded error morphisms are proved in Lean. A standalone checked
calculation also normalizes bounded lower-dot sectors into a filtered coefficient
image. The standalone calculation now also constructs endpoint label reindexing
and the signed unit-column comparison between two arbitrary choices. Its
coefficient-linear extension and triangular injectivity are not yet formalized;
none of these results establishes independence.

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

## The remaining choice comparison

For complete unique choices `F,G`, identify their matching classes by the
endpoint pairing, and transport strand counts with
`matchingStrandEquivOfIso` in `DecoratedNormalization.lean`. The desired statement is

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
skeletons; the signed comparison between two families is now checked standalone.

## Filtered lower-dot normalization

The standalone checked file
[`MatchingDotFiltration.lean`](../../scripts/Nondegeneracy/MatchingDotFiltration.lean)
defines `MatchingBasisChoice.openDots` as the finite sum of the actual strand
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
`exists_canonical_strand_dots`, and `labels_filtered_signRel`. The standalone results are not yet part of the
imported library API. The extension passes standalone compilation with warnings
as errors; its printed axiom dependencies are exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## From a bounded comparison to an inverse

Once those vectors are chosen, extend each unit-coefficient column to
coefficient `p` by multiplying its entries on the right by `p`. Thus an
entry `d` becomes `d*p`, not `p*d`; `rightAction_mul` proves the evaluation
identity. Do not choose a new arbitrary preimage separately for every `p`
and then assert linearity.

After relabeling and diagonal rescaling the transition would be `Id + L`,
where every column is finite and `L` strictly lowers the lexicographic
complexity. This gives local nilpotence: well-founded induction bounds the
depth of each column by the maximum depth of its finitely many children.
There is no uniform exponent for all labels, and dropping the crossing
count may increase the dot count arbitrarily. The finite geometric inverse
on each vector would then give an invertible coefficient transition.

That would equate injectivity for different choices. It would not prove
injectivity for any choice, nor replace the missing upward SKM independence
with full bubble coefficients. Independently chosen reverse expansions
need not be the inverse of the first transition.

## A smaller endpoint sufficient for independence transfer

An explicit inverse is stronger than needed for the nondegeneracy implication.
Once the signed triangular columns and their coefficient-linear extension `T`
are available, `T` is injective by a finite-support argument. If `x ≠ 0`, choose
the largest lexicographic complexity among labels in its finite support. At that
complexity, all strict-lowering columns contribute zero; distinct source labels
have distinct reindexed leading labels. The leading coefficient is multiplied by
`1` or `-1`, so cannot vanish. Thus `T x ≠ 0`, over an arbitrary ground ring.

Consequently, `expansion_F = expansion_G ∘ T` transfers injectivity of
`expansion_G` to `expansion_F`. Repeating the argument with the families reversed
gives equivalence of their injectivity statements without formalizing a locally
nilpotent inverse. The inverse remains a useful optional strengthening, but is
not on the shortest path to choice-independent nondegeneracy. This argument is
conditional on the still-unconstructed coefficient-linear extension of the
checked signed columns; it is not a proof of upward independence.

## Construction of a unit column (checked standalone)

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
or uniqueness of the error coefficients is used. This is now checked as `labels_filtered_signRel` in the standalone script.
Its axiom dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`.
The resulting full transition still needs its finite-support linear extension
and triangular injectivity formalized.
