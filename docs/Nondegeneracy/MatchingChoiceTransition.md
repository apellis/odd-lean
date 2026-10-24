# Crossing-filtered expansions and matching choices

Crossing-filtered coefficient extraction and the unit-leading signed comparison
with explicitly bounded error morphisms are proved in Lean. The lower-dot
coefficient recursion and invertible change-of-choice map are not yet constructed;
neither proved result establishes independence.

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
The explicit lower-dot coefficient vectors and the resulting decorated
comparison still need to be extracted.

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
