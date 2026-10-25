# Reduction from upward independence

## Status and decision

**Checked reduction; upward independence remains an explicit hypothesis.**
`SKM.nondegeneracy_of_upward_independence` proves the implication via contextual
descent (route A), and `nondegeneracy_iff_upward_independence` proves equivalence.
This does not establish upward independence or unconditional odd/mixed
nondegeneracy. The graded-dimension route (B) is an unused alternative; the
even comparison basis is not reused for odd colours.

The desired input is injectivity of every upward expansion at every external weight,
with coefficients in the abstract `SYM D k`, not merely scalar coefficients or the
image of `betaSYM`. The output is `SKM.NondegeneracyConjecture cs`. Route A itself
needs neither a field nor homogeneity, so it preserves any generality available in
the upward input. The programme's symmetrizable finite-colour field scope is included.

## A. Contextual descent

| Step | Existing declarations / missing work | Size and risk |
| --- | --- | --- |
| Sort both signed boundaries, deleting an equal-colour pair in correction terms | `ContextualBoundary.boundary_induction`, `nondegeneracy_of_contextual_descent` | Checked assembly; small final application |
| Sorted families from upward families | `WeakMate.sorted_independence` | Checked, including full coefficients |
| Change matching representatives and dot placements | `expansion_injective_choice_iff` | Checked; no preferred choice is a new premise |
| Distinct-colour target exchange | `distinct_target_exchange_descent` | Checked |
| Distinct-colour source exchange | `distinct_source_exchange_descent` | Checked with complete source choices and literal prefix serializers |
| Same-colour target families | `exists_same_colour_adapted_choices`, `exists_same_colour_adapted_equiv` | Constructed: complete families, literal unpaired terminal crossings, and common residual cup serializers |
| Same-colour target coefficient columns | `same_colour_target_exchange_descent`, `target_exchange_descent` | Checked at every height, retaining inverse-block corrections |
| Same-colour source families and columns | `exists_source_same_colour_adapted_equiv`, `same_colour_source_exchange_descent`, `source_exchange_descent` | Checked: full-SYM twists, negative-height low-cup components and downward-dot odd-bubble correction |
| Final implication | `nondegeneracy_of_upward_independence` | Checked; no remaining descent hypothesis |

The difficult point is **not** cancellation of an odd bubble. Every pivot must be a
unit scalar, possibly followed by `SYM.parityTwist`. Closed correction diagrams are
coefficients on the shortened boundary `L ++ Q`; their presence cannot be discarded.
For positive target height, low cup-dot counts are killed by the principal crossing
and detected by the identity components of the inversion matrix. For nonpositive
height, the principal pivot has a shifted index and the inverse-block terms lie
strictly below it. The source cases reverse the height inequality.

The first risk-reducing construction is now in `CupCompletedChoice` and
`AdaptedSameColourChoices`: unpaired representatives and literal residual cups
combine into two complete matching choices. The equivalence in
`exists_same_colour_adapted_equiv` identifies their unpaired sectors and embeds
the common paired sector as `ℕ × B.Labels`. The source counterparts are
`SourceCompletedChoice` and `SourceAdaptedChoices`. Their actual columns are
attached and detected by the source and target descent theorems. Residual
serializers use `PointedMatching.ofStrict` on `B.members`, assembled through
`strictResidualChoice`; their layers are not identified with arbitrary original
serializers of `B`.

## B. Bending and graded dimensions

The even model is Khovanov--Lauda, *A categorification of quantum sl(n)*,
arXiv:0807.3250v1, §3.2.3: Proposition 3.12 counts the spanning diagrams; Corollary
3.14 bounds graded dimensions; Remark 3.16 reduces nondegeneracy to positive words.
The declaration `KL3.Diagram.cor_3_13` uses a different numbering from that edition:
its mathematical role is the graded-dimension upper bound, not printed Remark 3.13.

The corresponding implementation is `KL3.Diagram.prop_3_12`, `cor_3_13`,
`calculusNondeg_iff`, `isSpanFamily_bendG`, `positiveNondeg_iff`, and
`calculusNondeg_of_positive`. The last theorem bends the source to the target,
uses the mixed inversion decompositions to establish a recursion in the target
word, and reduces normally ordered words to upward Hom spaces.

The super analogue would require the following.

| Step | Existing material / missing work | Size and risk |
| --- | --- | --- |
| Graded spanning and local finiteness | `MatchingBasisChoice.expansion_surjective`, `hom_laurentian`, `hom_parity_laurentian` | Checked; finite colours imply `Symmetrizer.DegreeLocallyFinite` |
| Abstract coefficient monomial basis | `SYM.coefficientBasis`, `polynomialExteriorEquiv`, `beta_coefficientBasis_mem` | Basis and parity checked for mixed data; integer-degree count still needs connection to the symmetrizer grading |
| Graded bending for arbitrary signed boundaries | Mate isomorphisms and graded presentation; even `isSpanFamily_bendG` is a model | Medium: degree shifts and super inverses must be proved for the actual SKM maps |
| Graded Hom decomposition from inversion | SKM inversion relations, contextual crossing maps | Medium to large: finite direct-sum maps with all degree and parity shifts |
| Expected-rank recursion | Even `prop_3_12` and `calculusNondeg_of_positive` are models | Large: mixed polynomial/exterior count and equality with the inversion recursion; cannot assume the desired Hom dimension formula |
| Recover injectivity from spanning and equal graded ranks | `EvenBridge.injective_of_surjective_of_basis` supplies the algebraic pattern | Small after the preceding data; field dimension comparison suffices |
| Integral extension | Even proof uses a comparison basis and degreewise Orzech | Separate obligation: field equality alone does not prove injectivity over arbitrary rings |

### Why exterior coefficients are not an obstruction to field dimensions

Use dimensions over the ground field, not a fraction field of `SYM` and not rank
over its even subalgebra. In a fixed degree, an ordered polynomial monomial times
an exterior monomial gives a finite candidate basis. Exterior generators occur at
most once, even in characteristic two (the square-zero relation is explicit).
Finite colours and positive symmetrizer degrees give only finitely many generators
of bounded degree. A fixed matching has finitely many strands; all dots raise
degree. There are finitely many matching classes for fixed boundaries, and the
undecorated degrees have a lower bound. Thus degreewise comparison is legitimate.
The already checked `hom_laurentian` proves local finiteness and boundedness below
without nondegeneracy, using spanning. It does not prove the required equality of
ranks.

Bending may shift degree and parity. Koszul signs are units and cannot change the
ordinary dimension of a graded piece, but the inverse map must contain the correct
signs. Forgetting parity after constructing a super linear isomorphism is safe;
using superdimension (even dimension minus odd dimension) to infer injectivity is
not. A nonzero even and odd kernel could have vanishing superdimension.

The even proof `EvenBridge.expansion_injective` has an independent comparison
basis in the even diagram category. It obtains a degreewise surjective square map
and applies Orzech's theorem. In the super setting, spanning alone supplies neither
a square map nor the comparison basis. Replacing that basis by the desired basis
would make the argument circular. Matching graded ranks must first follow from
upward independence and the signed inversion recursion.

## What is and is not settled

There is no counterexample to the upward reduction here. Route B is not rejected
mathematically. It is deferred because its additional rank-recursion interface is
larger than the explicit descent interface, while route A also avoids field
and grading restrictions. Route A now proves the headline implication. What
remains for unconditional nondegeneracy is upward independence itself: the
categorical action and coefficient-detection obligations in `GeneralRoute.md`,
not an additional oriented-descent assumption.
