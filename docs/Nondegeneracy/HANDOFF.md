# Odd nondegeneracy: restart state

Branch `research/odd-nondegeneracy`. Rules for this branch: `AGENTS.md`, "Workflow and
evidence". This file is updated in the same push as the results it describes. Status
words: *Lean* means compiled on this branch and covered by full CI; *proposed* means a
written argument in `docs/Nondegeneracy/` that is not checked; *open* means neither.

Target: [BE2] §8 Nondegeneracy Conjecture (`SKM.NondegeneracyConjecture`), i.e.
injectivity of `MatchingBasisChoice.expansion` over the abstract `SYM` (polynomial even
generators, exterior odd generators), for odd and mixed data. No full nondegeneracy
theorem is claimed.

Scope: compatible symmetrizable Cartan superdata with finitely many colours and homogeneous
scalars, over a field, followed by integral descent as in the even case. Nonsymmetrizable data
and nonhomogeneous scalars are outside the target.

Route: the super analogue of Webster's proof of the even case (formalized in
categorification-lean): deformed cyclotomic super actions with ELV odd parameters at highest and
lowest weight, the family `Hom(T(-μ₊), W(μ₋))` reaching every weight `μ₋ - μ₊`, detection of the
upward part and of bubble products there, and the reduction of the conjecture to upward
independence. Proposed theorem graph: [GeneralRoute.md](GeneralRoute.md). The product-datum Hom family
must still be fused to the original superdatum. The exact test in
`scripts/Nondegeneracy/nilpotent_hom_fusion.py` refutes zero/zero fusion with
inherited blockwise dots: the necessary odd crossing equation has coefficient
rank 32 and augmented rank 33. The separated zero/nonzero alternative remains
proposed and retains all odd coefficients in one connected reservoir, not in
the invertible probe; its all-content categorical inversion is still open.

`separated_fusion_relations.py` checks zero/nonzero cross-polynomial units in
all colour-parity combinations, including a nonsemisimple probe. Its adjacent
odd affine A1 test includes one reservoir i strand, one probe i strand and one
reservoir j strand: all six labelled shuffles satisfy the two-strand relations
and the two nonzero repeated-colour braid corrections. Both independent
reservoir exterior generators survive. This is an affine corner test, not an
induction/restriction construction or an all-content inversion theorem.

## Proof architecture

| Step | Statement | Status |
| --- | --- | --- |
| Assembly | sorted-boundary independence + source exchange descent + target exchange descent imply the conjecture | Lean: `SKM.nondegeneracy_of_contextual_descent` |
| Sorted boundaries | full upward independence implies independence of every sorted family `(ups u ++ dns r, dns l ++ ups v)`, at every external weight, over full `SYM` | Lean: `WeakMate.sorted_independence` (no action, field, finite-colour or faithfulness hypothesis) |
| Choice independence | expansion injectivity does not depend on the permitted choice of representatives, points and serializers | Lean: `expansion_injective_choice_iff` |
| Target exchange, distinct colours | `TargetExchangeDescent` for `i ≠ j` | Lean: `SKM.distinct_target_exchange_descent` |
| Source exchange, distinct colours | adapted families and their coefficient map | Lean: `distinct_source_adapted_independent`, `distinctSourceExchange_coefficient`; the descent step itself is open |
| Target exchange, same colour | requires the residual deletion `L ++ Q` | open |
| Source exchange, same colour | as above | open |
| Upward independence | finite observations at fixed weight imply `UpwardIndependence` | Lean: `upward_independence_of_finite_observations` |
| Cyclotomic separation | cofinal colourwise cutoffs jointly detect the full coefficient-extended Hom with fixed spectators; a degree-bound criterion for moving spectators | `cofinal_elv_quotients_with_spectators_detect`, `spectator_images_detect_of_bounds`; moving-family hypotheses remain open |
| Observations | extracted regular-projective evaluation on words including spectators; joint algebraic detection remains an input | `SpectatorEvaluation`, `upwardCoefficientMap_injective_of_spectators`; [SpectatorDetection.md](SpectatorDetection.md) |
| Multicolour deformed action | KKO-type cyclotomic action with ELV odd parameters, even cutoffs at odd colours | proposed: [MulticolourActionTheorem.md](MulticolourActionTheorem.md) |

## Reduction route comparison

[ReductionRoute.md](ReductionRoute.md) compares contextual descent with a graded-dimension
reduction. The proposed next route is contextual descent: reconstruct complete same-colour
adapted choices, then their coefficient columns. `hom_laurentian` already supplies the
finite-dimensionality needed by the alternative field route; the missing super rank recursion
and comparison basis prevent treating the even Orzech argument as an immediate reduction.

`exists_cup_completed_choice` constructs a complete choice from unpaired representatives
and literal cups on a complete residual family, with a sum-label equivalence and exact
layer equations. `exists_choice_with_literal_cups` constructs its inputs from arbitrary
complete choices, with no independence premise. Both orientations with nonempty contexts
are exercised in `CupCompletedChoiceExamples.complete_paired_sector`.
`exists_same_colour_adapted_choices` and `exists_same_colour_adapted_equiv` now
construct simultaneous complete same-colour target choices: a single label
equivalence, literal unpaired terminal crossings, and a common paired embedding
`ℕ × B.Labels` with both cup serializers. Their coefficient comparisons remain open.

## Action review

[ActionReview.md](ActionReview.md) is a proposed source comparison of the seven
steps of the even-cutoff argument. The normality, balanced-ideal, norm and cap-row
repairs survive; the explicit comparison from the super-opposite induction
endomorphisms to the specified upward presentation remains open. Ordinary reversal
for projectivity and super-opposite reversal for natural transformations must not
be identified. No multicolour action is yet claimed in Lean.

[OddCutoffAction.md](OddCutoffAction.md) gives a proposed exterior-translation
reduction for odd cutoffs: `f_i=(x-d_i)C_i(x²)`, with no top-coefficient relation.
The normalizing automorphism acts by parity on coefficients and is involutive;
copying the even-cutoff inverse twist gives the wrong sign. The relative action
extension preserves inversion by triangular dot-row changes. Its unconditional
use still requires the all-content diagram and presentation comparison.

[LowestWeightAction.md](LowestWeightAction.md) records that the proposed
`E=induction`, `-Λ+β` convention is already lowest weight. The opposite orientation
is proposed by signed Chevalley transport into the super-opposite target, reusing
`SKM.chevalleyTwo`. The Hom construction instead reverses one lowest-weight factor
horizontally; it gives two copies of the datum, not their fusion. A nonzero Hom
vacuum and original-datum fusion remain separate requirements.

[ActionLeanPlan.md](ActionLeanPlan.md) orders the proposed construction from
signed induction presentation comparison and simultaneous exterior translation,
through balanced quotients, projectivity, inversion, the action, opposite transport
and the product-datum Hom family. Each module names a consumer and existing
inputs. The next bounded action result is the signed mixed-colour presentation
comparison, not a new abstract action interface.

## Open obligations

1. **Same-colour exchange descent**, source and target. The distinct-colour target proof is
   the template; the equal-colour case must absorb the residual deletion term and its bubble
   corrections.
2. **Distinct-colour source descent**: assemble `SourceExchangeDescent` for `i ≠ j` from the
   adapted-family results above.
3. **The observation interface.** `FiniteUpwardObservations μ t t'` asks for maps into the ELV
   quotient of the coefficient category on the words `t, t'` alone. Over a field it follows from
   upward independence at `μ` (compose the quotient map with the inverse of the coefficient map),
   so it is a restatement of the target, not a weaker statement. An action at lowest weight `-Λ`
   evaluates `E_t 1_μ` only after adding spectator strands `s` with `μ = -Λ + wt(s)`, and `μ` is
   fixed while the cutoff grows. The separation theorem therefore has to be extended to
   cyclotomic quotients with spectators, or the interface restated, before an action can
   discharge it. `SpectatorEvaluation` now states the regular-projective component with
   a specified affine whiskering and bubble lifts on the whole word. Its product law and
   joint detection are still open for an action-derived family. The conditional consumer
   `upward_independence_of_spectators` makes neither of those assertions. Fixed-spectator
   cofinal quotient separation is proved, but does not allow the spectator word to grow
   with the cutoff. The existing quadratic crossing-loss bound fails whenever total
   strand number `n ≥ 3` and cutoff `N ≤ 2n` (`spectator_crossing_bound_obstruction`).
   The next target is a sharper spectator-corner theorem or a fixed-weight reservoir-vacuum
   extraction; neither the failure of this bound nor separate bubble independence decides
   joint detection.
4. **The deformed action.** Independent review of the proposed even-cutoff theorem, in
   particular the balanced maps, the norm audit and the parity conventions of the
   negative-height cap conversion; extension to odd heights at odd colours (the parity of
   `⟨h_i, Λ⟩` is constant on a root-lattice coset when `i` is odd); bubble images at a fixed
   weight with spectators.
5. **Fixed-weight coverage.** Dominant weights are cofinal in each root-lattice coset only in
   finite type, and there odd colours occur only at the short end of `B_n`, never adjacent.
   For general symmetrizable data every weight is `μ₋ - μ₊` with `μ±` dominant, reached by the
   family `Hom(T(-μ₊), W(μ₋))` as in the even case; the super version of that family, and the
   joint detection of the odd bubbles of adjacent odd colours in it, are open. For odd `i`,
   `⟨h_i, μ⟩ mod 2` is constant on root-lattice cosets, so odd cutoffs at odd colours are needed.

## Next targets

These statements were proved by the methods recorded in the linked notes but are not yet on
this branch:

- all-height paired target coefficient columns; source crossing state and point transport;
  contextual source-cap families (complete same-colour target adapted choices are now in Lean)
  ([ContextualSorting.md](ContextualSorting.md), [SourceContextualSorting.md](SourceContextualSorting.md));
- bounded ELV coefficient recovery with locally triangular inversion, and nilpotence of the
  coefficient dot ideal ([UpwardSeparation.md](UpwardSeparation.md));
- odd Frobenius resolvent identities beyond `FrobeniusResolvent`, and the first separated-sector
  chart lemmas ([SpectralCompensation.md](SpectralCompensation.md));
- the parity involution on the coefficient basis and the source/target `β` placement identity;
  the negative-height cap-row conversion ([MulticolourCyclotomicAction.md](MulticolourCyclotomicAction.md)).

## Mathematical guardrails

- Abstract `SYM` has a distinct exterior generator for each odd colour. Spectator strands do
  not show that categorical bubbles realize those generators.
- Signed choice transitions lower crossing/open-dot complexity; closure transport adds dots at
  fixed crossings. Do not conflate the two orders.
- Right coefficient extension uses `d*p`, not `p*d`.
- Inverting an even ELV constant kills the odd parameter of that factor
  (`CyclotomicExteriorObstruction`); separate nilpotent factors are not excluded.
- Squared-dot spectral blocks preserve parity; odd-dot scalar eigenblock compression is not a
  multiplicative coefficient detector.
- The odd intertwiner has norm `-(y²-x²)²(x²+y²)`; generic transport needs both difference and
  sum units.
- At even cutoffs the cyclotomic element is normal, not central: `ν(x) = x - 2d`, and right
  multiplication uses `ν⁻¹(x) = x + 2d`. KKO's centrality step does not apply verbatim.
- [ELV] Theorem 4.5 supplies the rank-one deformed action with odd coefficients and
  Proposition 4.7 its bubble values; the universal-equivalence part of that proof uses rank-one
  nondegeneracy and must not be used circularly.
- The isomeric Heisenberg action is reduced (odd bubble zero) and cannot detect exterior
  coefficients by itself.
- The two-colour connected degree-two model has `δ_i δ_j ≠ 0` but `(reverse crossing)·δ_i δ_j = 0`,
  so joint detection of crossings and bubble products is a separate requirement.
- Finite Python models in `scripts/Nondegeneracy/` test particular instances; none is a proof of
  a general statement.

## Notes

[PROGRESS.md](PROGRESS.md) (status board), [OrientedReduction.md](OrientedReduction.md),
[MatchingChoiceTransition.md](MatchingChoiceTransition.md), [UpwardSeparation.md](UpwardSeparation.md),
[MulticolourActionTheorem.md](MulticolourActionTheorem.md),
[MulticolourCyclotomicAction.md](MulticolourCyclotomicAction.md),
[SpectralCompensation.md](SpectralCompensation.md), [CoupledBubbleEvaluation.md](CoupledBubbleEvaluation.md),
[OddUnfurling.md](OddUnfurling.md), [RewritingAlternative.md](RewritingAlternative.md).
