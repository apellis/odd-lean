# Odd nondegeneracy: restart state

Branch `research/odd-nondegeneracy`. Rules for this branch: `AGENTS.md`, "Workflow and
evidence". This file is updated in the same push as the results it describes. Status
words: *Lean* means compiled on this branch and covered by full CI; *proposed* means a
written argument in `docs/Nondegeneracy/` that is not checked; *open* means neither.

Target: [BE2] §8 Nondegeneracy Conjecture (`SKM.NondegeneracyConjecture`), i.e.
injectivity of `MatchingBasisChoice.expansion` over the abstract `SYM` (polynomial even
generators, exterior odd generators), for odd and mixed data. No unconditional full nondegeneracy
theorem is claimed. B0 is complete: `nondegeneracy_of_upward_independence` derives
the conjecture from upward independence at every weight; the latter remains open.

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
[SeparatedFusion](SeparatedFusion.md) gives the proposed local denominator
argument, the conditional all-height Schur argument and an explicit Lean plan.
The categorical multicolour Hom-sector comparisons and their actual mate
coordinates remain open; no all-content A2 theorem is claimed.
`commute_inverse_square_difference` and `separated_diagonal_crossing` prove
in Lean that `(x-y)/(x²-y²)` has both odd dot slides and square
`(x²+y²)/(x²-y²)²`. The smallest actual nonvacuum rank-one mate was rechecked:
its 72-by-72 matrix has determinant one, with square-zero feedback of rank four.

## Super Rouquier interface

`OddMath/SKM/RouquierData.lean` defines `RouquierData`, `RouquierFamily`,
`SuperAdjunction`, `SuperRouquierLoc`, and the homogeneous matrix interfaces
`SuperSumInvTo`/`SuperSumInvFrom`. The ambient `TwoSupercategory` retains
super-interchange; it is not an ordinary bicategory. The common inverse
component has parity `|i|`, and dotted identity component `n` has parity
`n |i|`; these are the explicit parity shifts of the formal direct sums.
`rouquierMate` is the ordered cup–crossing–cap composite. `boundaryPos_eq`
and `boundaryNeg_eq` consume its inverse to obtain the normalized Kronecker
window. These declarations pass the scoped warning-free build; full CI
remains the branch-wide verification gate.

`OddMath/SKM/RouquierHom.lean` constructs the linear parity-preserving
`homPre`/`homPost` functors on full Hom supercategories, their homogeneous
`SuperNatTrans` transformations, and `homSectorInterchange`. Its
`homSector_exchange` theorem retains the Koszul sign for opposite-sector
transformations; two odd transformations anticommute. This is the Hom-sector
generator layer, not multicolour affine coherence or categorical fusion.

`OddMath/SKM/RouquierHomAdjunction.lean` proves `homPostAdjunction` and
`homPreAdjunction`, including both triangles and evenness of all unit/counit
components. Precomposition reverses the two adjoints. The proof uses the even
underlying bicategory only for triangle coherence; the functors and naturality
remain on the full Hom supercategories. Content-dependent parity-shifted
comparisons and the coupled affine action remain to be constructed.

`OddMath/SKM/RouquierBoundary.lean` adds the actual finite dotted-unit
`RouquierBoundary.Coefficients`. `Coefficients.ofVacuumInverse` extracts it
from negative local inversion when the common summand vanishes.
`Coefficients.cap_mem`, `cup_cap`, and `hom_ext` prove the cap parity,
normalized top-coefficient pairing, and boundary detection. The cutoff-two
odd example has an odd cap; no unshifted opposite adjunction is inferred.

`OddMath/SKM/RouquierMate.lean` identifies the ordered `rouquierMate` with
`homMateEquiv`, proves both strand naturality laws, and derives
`rouquierMate_slide` from the upward dot slide without any inversion
hypothesis. Its interface consumer is `SuperRouquierLoc.mate_slide`:
`σ ≫ (x₂ ▷ F₂) - q • ((F₁ ◁ x₁) ≫ σ) = ε₁ ≫ η₂`.
The proof retains odd crossings; only the even prefix and suffix use ordinary
coherence. This is the unprojected categorical recurrence. Identifying its
sector projections with both ordered finite formulas is still missing.

`OddMath/SKM/RouquierSchur.lean` supplies associative block factorization,
`isUnit_of_schur`, and `isUnit_of_nilpotent_feedback`. Nilpotence concerns
the whole feedback operator. This removes the need for a commutative
coefficient determinant in the algebraic lifting step, but does not identify
the actual fused mate or its feedback. A2 remains open at the super analogue
of `RouqCoproduct.rouqSig_eq`, followed by the all-content negative-window and
nilpotent-ideal comparison; see SeparatedFusion §7. No separated-fusion
counterexample is asserted, and no fused inversion is assumed to prove A2.

This is the factor-action interface, including same-colour square, braid,
and local inversion. Multicolour affine relations and distinct-colour mixed
inversion are separate obligations. In particular no construction of a
fused action or theorem A2 is asserted. Detection still requires the bubble
normalization outside the finite inverse window and its comparison with the
connected reservoir coefficients.

## One-strand cyclotomic algebra coordinates

`QuiverHecke/CyclotomicAbsentColour.lean` proves `singlePolynomialEquiv` for
the existing quiver Hecke one-strand endomorphism algebra, including odd
colours. `singleCyclotomicEquiv` identifies its polynomial-ideal quotient
with `AdjoinRoot`; `singleCyclotomicFinEquiv_apply` gives the monic finite
coordinate map as the sum of scalar multiples of descended dot powers.
These are underlying-algebra results over any commutative ring. A super
quotient requires homogeneous polynomials. The superfunctors and adjunction
are constructed below; KKO local inversion remains open.
[ActionLeanPlan.md](ActionLeanPlan.md) places exterior ELV coefficients after
the even-parameter action theorem, and targets the existing
`SKM.SuperRouquierLoc` rather than a second local-data interface.

`QuiverHecke/CyclotomicAction/Quotient.lean` equips the existing finite-support
Hom algebra with a unit for finitely many colours, defines its genuine
two-sided first-dot polynomial ideal, and constructs `CyclotomicAlgebra` and
`cyclotomicMk` at every positive strand number. `cyclotomicMk_generator`
proves that the defining cyclotomic polynomials vanish. This supplies the
underlying quotient algebra; its homogeneous grading is supplied below.
The projectivity and Mackey statements needed for inversion remain open.

`CyclotomicAction/Induction.lean` constructs `appendAlgebra` by actual right
whiskering of affine Hom entries, proves `appendAlgebra_mem_ideal`, and
obtains the descended nonunital algebra map `cyclotomicAppend`. The associated
`cyclotomicInduction` is a genuine induction functor on underlying modules.
These inclusions run from height `n+1` to height `n+2`; the vacuum map remains
separate. The supermodule enhancement is given below. No ordinary
naturality claim is made for odd dots.
`CyclotomicAction/Restriction.lean` adds `cyclotomicRestriction` as truncation
by the unit-image idempotent and proves the underlying module adjunction
`cyclotomicIndResAdjunction`, without a flatness hypothesis. Its unit and
counit are those of the actual descended nonunital map, not assumed maps.
This underlying construction is distinct from the super adjunction below
and does not prove KKO inversion.
`CyclotomicAction/Slides.lean` proves the actual affine signed naturality
`induction_dot_slide`; `induction_dot_slide_odd` specializes it to the minus
sign for an odd new dot and an odd lower morphism. This supplies the corrected
homogeneous intertwiner equation rather than the false unsigned equation.
`CyclotomicAction/Parity.lean` equips affine `Hn` with its parity grading
independently of any integer symmetrizer. The coefficient-support condition
`CyclotomicPolynomialParity` proves homogeneity of the actual first-dot
polynomial generators and, in `cyclotomicIdeal_homogeneous_of_polynomials`,
of the entire two-sided ideal. Right multipliers are decomposed into
homogeneous parts; they are not silently assumed homogeneous.
`CyclotomicAction/SuperQuotient.lean` now descends that parity to the actual
`CyclotomicAlgebra`, with `cyclotomicParity_graded`, homogeneous affine lifts,
and `cyclotomicAppend_parity`. `CyclotomicSupermodules` is the existing
superbimodule category with trivial right scalar algebra. These constructions
do not replace the quotient by a polynomial model or forget its odd part.
`CyclotomicAction/SuperInduction.lean` constructs the actual colour-cut
superbimodule `inductionCorner = B φ(1)` and its balanced-tensor
`cyclotomicSuperInduction`. This is an additive, `k`-linear superfunctor,
including on odd morphisms, using the signed tensor whiskering.
`CyclotomicAction/InductionComposition.lean` constructs `compositionCorner`
with right action through the composite inclusion and proves the even
superbimodule isomorphism `inductionCompositionIso : C eᵢ ⊗_B B eⱼ ≅ C φᵢ(eⱼ)`.
Its forward map is `x ⊗ y ↦ x φᵢ(y)` and its inverse is `z ↦ z ⊗ eⱼ`;
both algebra actions and both parity compatibilities are proved. The scoped
warning-free build and declaration axiom audit pass. This supplies coordinates
for composing two positive-height inductions, not crossing, braid or KKO
inversion relations.
`CyclotomicAction/LastCrossing.lean` constructs the finite matrix sum
`cyclotomicLastCrossing` from the literal last-pair crossing `[i,j] → [j,i]`.
It proves parity `|i||j|`, both colour-cut identities and signed intertwining
`θᵢⱼ(r) τ = (-1)^{|r||i||j|} τ θⱼᵢ(r)` for the two composite inclusions.
Rows are targets, so right multiplication goes from `C θᵢⱼ(1)` to
`C θⱼᵢ(1)`. The scoped warning-free build and declaration axiom audit pass.
`CyclotomicAction/SuperCrossing.lean` now constructs the homogeneous map
`compositionSuperCrossing : compositionCorner i j ⟶ compositionCorner j i`,
with parity `|i||j|` and formula `x ↦ (-1)^{|i||j||x|} x τ` on homogeneous
inputs. Signed left linearity and ordinary right linearity follow from the
proved global intertwiner, not an assumed relation. Its scoped warning-free
build and declaration axiom audit pass. Square, braid and inversion relations
remain separate obligations.
`CyclotomicAction/InductionFunctorComparison.lean` constructs the even natural
isomorphism `inductionFunctorComparison` from successive cyclotomic induction
to tensoring by `compositionCorner`. Its pure-tensor formula is
`x ⊗ (y ⊗ m) ↦ (x φᵢ(y)) ⊗ m`; the inverse uses the existing balanced-tensor
associator and the proved corner isomorphism, with no inverse hypothesis.
`CyclotomicAction/CrossingTransformation.lean` transports
`compositionSuperCrossing` along these comparisons to
`cyclotomicSuperInductionCrossing`, a supernatural transformation between the
two orders of composed induction, homogeneous of parity `|i||j|`.
Signed naturality holds on the full supermodule categories. Both modules pass
the scoped warning-free build and owned-declaration axiom audit. Square,
braid and inversion relations, and the KKO decomposition, remain open.
`CyclotomicAction/SuperRestriction.lean` similarly represents restriction by
`restrictionCorner = φ(1) B`; `cyclotomicSuperRestriction` is additive,
`k`-linear, and parity preserving. The positive-height indexing still leaves
the vacuum step separate; the KKO decomposition is not proved.
`CyclotomicAction/CornerPairing.lean` gives even superbimodule maps
`cornerEvaluation : B e ⊗_A e B → B` and
`cornerCoevaluation : A → e B ⊗_B B e`, together with the two elementary
idempotent triangular identities. These use actual multiplication in the
cyclotomic quotient.
`CyclotomicAction/SuperAdjunctionUnit.lean` constructs the even natural
transformation `cyclotomicSuperUnit`, from the identity to induction followed
by restriction, i.e. each module maps into `e B ⊗_B (B e ⊗_A M)`. Naturality is proved
for odd as well as even module maps; both inserted idempotents have parity
zero.
`CyclotomicAction/SuperAdjunctionCounit.lean` constructs
`cyclotomicSuperCounit` by `(x ⊗ (y ⊗ m)) ↦ (xy)m`. Its naturality proof
accounts for both tensor-whiskering signs and the signed left-linearity of
an odd supermodule map.
`CyclotomicAction/SuperAdjunction.lean` proves both triangular identities and
bundles `cyclotomicSuperIndResAdjunction`. Both directions of its Hom
bijection preserve parity. This is an actual super induction-restriction
adjunction, not only the underlying ordinary adjunction. Remaining action
obligations are the vacuum inclusion, the square, braid and mixed
comparisons for the constructed dot and crossing transformations, and the
projective Mackey/local-inversion theorem with the prescribed parity shifts.

`CyclotomicAction/LastDot.lean` constructs `cyclotomicLastDot` as the image
of the finite diagonal sum of rightmost dots on words ending in the induction
colour. `cyclotomicLastDot_parity` proves parity `D.parity i`, and
`cyclotomicLastDot_corner` proves both unit-image corner identities without
a polynomial-parity hypothesis. `cyclotomicLastDot_comm` proves
`φ(r)c = (-1)^(p |i|) c φ(r)` for every parity-`p` quotient element, using
homogeneous affine lifts. The indexing is height `n+1` to height `n+2`.
`CyclotomicAction/SuperDot.lean` constructs `inductionSuperDot` on this
corner: on homogeneous `x` it is `(-1)^(|x| |i|) x c`, as proved by
`inductionSuperDot_apply`. The concrete last-dot relation gives ordinary
right linearity; the parity sign gives signed left linearity.
`inductionSuperDot_parity` proves degree `|i|`, and balanced-tensor signed
interchange gives `cyclotomicSuperInductionDot`, a `SuperNatTrans` on
`cyclotomicSuperInduction`, homogeneous of degree `|i|`. These declarations
pass the scoped warning-free build. Square, braid, crossing and KKO
comparisons remain open; unsigned right multiplication is not substituted
for the signed-left superbimodule convention.

`CyclotomicAction/ActionSupercategory.lean` packages these supermodule
categories as `cyclotomicActionObject` in the existing `SCat` 2-supercategory,
with bundled target `cyclotomicActionTarget : TwoSCat k`.
`cyclotomicActionInduction` and `cyclotomicActionRestriction` are its
1-morphisms; `cyclotomicActionAdjunction` inhabits the existing
`SKM.SuperAdjunction` and proves both triangles with even unit and counit.
`cyclotomicActionDot_mem` gives the colour parity of its dot 2-endomorphism.
No local inversion or new action interface is assumed. The concrete
positive-height adjunction, dots and crossings above form the action data,
not yet a representation satisfying all defining relations. Vacuum extension
and the parity-shifted Mackey decomposition remain open.

## Proof architecture

| Step | Statement | Status |
| --- | --- | --- |
| Assembly | sorted-boundary independence + source exchange descent + target exchange descent imply the conjecture | Lean: `SKM.nondegeneracy_of_contextual_descent` |
| Sorted boundaries | full upward independence implies independence of every sorted family `(ups u ++ dns r, dns l ++ ups v)`, at every external weight, over full `SYM` | Lean: `WeakMate.sorted_independence` (no action, field, finite-colour or faithfulness hypothesis) |
| Choice independence | expansion injectivity does not depend on the permitted choice of representatives, points and serializers | Lean: `expansion_injective_choice_iff` |
| Target exchange, distinct colours | `TargetExchangeDescent` for `i ≠ j` | Lean: `SKM.distinct_target_exchange_descent` |
| Source exchange, distinct colours | complete adapted families and native coefficient twist | Checked: `distinct_source_exchange_descent` |
| Target exchange, same colour | requires the residual deletion `L ++ Q` | Checked: `same_colour_target_exchange_descent` |
| Source exchange, same colour | requires the residual deletion `L ++ Q` | Checked: `same_colour_source_exchange_descent` |
| B0 headline | upward independence at every weight implies the full conjecture | Checked: `nondegeneracy_of_upward_independence`; also `nondegeneracy_iff_upward_independence` |
| Upward independence | finite observations at fixed weight imply `UpwardIndependence` | Lean: `upward_independence_of_finite_observations` |
| Cyclotomic separation | cofinal colourwise cutoffs jointly detect the full coefficient-extended Hom with fixed spectators; a degree-bound criterion for moving spectators | `cofinal_elv_quotients_with_spectators_detect`, `spectator_images_detect_of_bounds`; moving-family hypotheses remain open |
| Observations | extracted regular-projective evaluation on words including spectators; joint algebraic detection remains an input | `SpectatorEvaluation`, `upwardCoefficientMap_injective_of_spectators`; [SpectatorDetection.md](SpectatorDetection.md) |
| Multicolour deformed action | KKO-type cyclotomic action with ELV odd parameters, even cutoffs at odd colours | proposed: [MulticolourActionTheorem.md](MulticolourActionTheorem.md) |

## Reduction route comparison

[ReductionRoute.md](ReductionRoute.md) compares contextual descent with a graded-dimension
reduction. Contextual descent is now complete, including actual complete source
and target choices and all coefficient columns. `hom_laurentian` already supplies the
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

## Reservoir-vacuum detection

The separated-sector consumer is now `FusedFixedWeightFamily`, not a family
of moving spectators. Conditional declarations in `ReservoirVacuumDetection`
derive the joint bounded observation identity from composition, connected
reservoir affine coordinates, and the named `NormalizedBubbleFormula` on the
elementary and exterior generators. They then apply bounded ELV separation to
obtain `upwardCoefficientMap_injective` at the same external weight and
`upward_independence_of_fused_fixed_weight_families` for the reduction.
`reservoir_parity_cutoffs_detect` covers arbitrary colourwise even/odd schedules.
`SpectatorEvaluation` remains the one-sector consumer and is not used to
supply the new family's coverage premise.

`ReservoirWeights` constructs cofinal paired cover levels with even probe
level, reservoir parity equal to the prescribed coroot pairing, and exact
level difference. `odd_pairing_invariant` proves invariance under signed root
words. `exists_weights_of_pairing_surjective` realizes the levels in a
pairing-complete lattice; `exists_extended_weights` does so for every datum
in the explicit extension `X × (I → ℤ)`, without changing its Cartan matrix
or parity. `ReservoirWeights.restrictRouquierFamily`, in the
`ReservoirWeightRestriction.lean` module, restricts the actual super
Rouquier factor interface along `μ ↦ (μ,0)`, retaining local inverses and
all parity shifts. Full multicolour action and fused-family construction
remain open.

`QuiverHecke.reservoirWindowCoordinates` in `ReservoirCoordinates.lean`
splits the bounded connected ELV injection over a field and recovers the
whole joint coefficient/PBW window.
`exists_bounded_reservoir_extraction` extends any linear source coordinate
map on that window, without a global finite-quotient automorphism. It does
not identify the regular quotient with the fused vacuum; the latter's
`affine_coordinates` law and normalization comparison remain open.

`SKM.reservoir_coefficients_recovered` proves finite triangular inversion of a
specified ordered probe convolution; `reservoir_exterior_recovered` removes a
unit factor from an odd coefficient. The categorical convolution and its
bounded coordinate comparison remain open, as does construction of the fused
family. The connected two-odd examples test the algebraic inputs, not family
existence. See [ReservoirVacuumDetection.md](ReservoirVacuumDetection.md).

## Action review

`CyclotomicAction.SignedMultipliers` checks the signed right-multiplier
composition and a nonzero rational matrix instance: negating both odd
crossings still changes a constant quadratic relation from 1 to -1.
[SignedInductionComparison.md](SignedInductionComparison.md) records the exact
scope. This rules out the uniform-sign, unchanged-parameter assignment, not
an action with a proved directed-sign or parameter comparison. The full
multicolour square and braid comparison remains open. The connected all-odd
`AsymmetricParameters` example has Cartan entries -2,-4 and `Q=u²+v⁴`:
no common crossing-product scalar absorbs the opposite signs of square and
fourth-power dot transport. A valid transported family `Q'=u²-v⁴` and its
conditional signed mixed-square transfer are checked. Thus directed signs
alone with unchanged parameters are insufficient in general; a full
parameter/presentation transport remains necessary.

[ActionReview.md](ActionReview.md) is a proposed source comparison of the seven
steps of the even-cutoff argument. The normality, balanced-ideal, norm and cap-row
repairs survive; the explicit comparison from the super-opposite induction
endomorphisms to the specified upward presentation remains open. Ordinary reversal
for projectivity and super-opposite reversal for natural transformations must not
be identified. No multicolour action is yet claimed in Lean.

`CyclotomicAction.Normality` checks the first-dot normality and inverse
balance equations for even cutoff, the square-zero deformation term and
conjugate square-annihilator, and the odd-cutoff normality and square.
These are ring identities with coefficient commutations and top-coefficient
annihilation explicit, not a constructed normalizing automorphism or a
balanced all-content bimodule. In particular the even inverse-balance dot
is `x+2d`, not `x-2d`. `LocalRelationExamples` checks both balances on
exterior creation/contraction matrices with `x²=1` and `d≠0`, and proves
that using the normalizer instead of its inverse fails. It also constructs
a single directed-sign crossing operator whose constant square is the identity.
Its headline axiom inventory uses only the permitted standard axioms.

[OddCutoffAction.md](OddCutoffAction.md) gives a proposed exterior-translation
reduction for odd cutoffs: `f_i=(x-d_i)C_i(x²)`, with no top-coefficient relation.
The normalizing automorphism acts by parity on coefficients and is involutive;
copying the even-cutoff inverse twist gives the wrong sign. The relative action
extension preserves inversion by triangular dot-row changes. Its unconditional
use still requires the all-content diagram and presentation comparison.

`CyclotomicAction.ExteriorTranslationRelations` proves simultaneous
mixed-dot anticommutation, invariance of arbitrary square-variable mixed
polynomials, and the entire alternating repeated-outer-colour braid
polynomial with a second translated odd middle colour. Its rational
four-dimensional exterior matrices retain a nonzero product of the two
parameters and supply mixed-dot and nonzero braid-correction consumers.
The category equivalence, strand-inclusion compatibility and cyclotomic
quotient descent have not been constructed.

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

## Strict residual serializers
**Strict residual choice interface (checked).** `StrictResidualChoice` rebuilds a complete matching choice using `PointedMatching.ofStrict` on every member. Its `strictResidualLabels` equivalence preserves the exact strict-serializer layers, and `strictResidualChoice_independent` transfers independence by choice invariance. Thus residual independence can be applied to the serializers used in cup completion without identifying them with an unrelated chosen serializer. Contextual same-colour descent is now checked on both sides as recorded below.

`exists_same_colour_cup_rows` now gives complete original, swapped, and residual choices together with the exact evaluated left- and right-cup rows at every dot count and external weight. The unpaired exchange equations are retained. `SameColourCupRowsExamples.complete_cup_rows` checks the interface for a two-colour odd datum over ℚ with both contexts nonempty; its axiom print contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Full contextual target descent

`same_colour_target_exchange_descent` derives independence of the original boundary from independence of its swapped and shortened residual boundaries. The proof kills unpaired coefficients using the actual inverse-crossing formulas modulo the paired output rows, then invokes `pairedExpansion_injective`; both height signs and the zero boundary are included. `target_exchange_descent` combines this with distinct-colour descent and proves the entire `TargetExchangeDescent cs` interface over any commutative coefficient ring admitted by `Sc`. No homogeneity, field, grading, action, or bubble-injectivity hypothesis is added. The concrete two-odd-colour consumer `SameColourTargetFrameExamples.all_target_exchanges` and both headline axiom prints use only the three permitted axioms. `source_exchange_descent` now proves the corresponding full `SourceExchangeDescent cs`.

`SourceFrozenSwap.ren` and `crit` preserve strand renaming and critical IDs. `SourceIdRelabel` now transports validity, full states, cap renamings, and critical lists through injective ID maps fixing fresh IDs; `reducedData_iff` preserves all reducedness data. A cap-containing consumer moves ID zero and checks the actual transports. `SourceCrossState.start_cross` identifies the actual initial-crossing state with the frozen transposition and initial-ID swap, retaining its cap-renamed history in `cross_run`. `SourceCrossAttachment.attach` supplies strict pointed representatives, actual count equivalences and literal initial-crossing serializers. `exists_adapted_pointed_pair` covers both crossing orientations. The complete source choices and coefficient descent use this transport as described in `SourceContextualSorting.md`.

`SourceCapState.start_cap` now identifies the exact initial-cap state, including the reversed frozen endpoints, surviving strand ID and fresh counter. `cap_matching`, `cap_strict`, `cap_layers`, `ren_cap` and `crit_cap` give validity, strictness, layer orientation and full suffix transport. The nonempty-context two-colour consumer checks these identities. `SourceCapAttachment` supplies the residual comparison by inserting the frozen pair and shifting fresh IDs by four. `attach` constructs actual cap-adapted pointed representatives, `cap_family_complete` proves coverage of every paired source class from a complete residual family, and `labelEquiv`/`attach_layers` provide the full count bijection and literal serializer compatibility. The fresh-cup and later-cap consumers check both creation and subsequent ID joins. `SourceCompletedChoice` now assembles the cap and unpaired sectors. `exists_source_same_colour_adapted_equiv` supplies complete choices, the full label equivalence and paired embedding with literal cap serializers on both sides; residual serializers are exactly `PointedMatching.ofStrict` on `B.members`. `exists_source_adapted_distinct_colour_choices` gives complete distinct-colour choices and both initial-crossing cases. These constructions add no independence hypotheses. `distinct_source_exchange_descent` now proves the distinct-colour source branch using these actual complete choices and `distinct_source_adapted_independent`, with the native full-SYM crossing twist. It requires only swapped-boundary independence. `SameColourSourceFrame.kernel_supported_paired` eliminates the unpaired kernel using the actual inverse crossing. `PairedSourceUpwardColumns`, `PairedSourceCupColumns` and `PairedSourceDetection` prove all-height paired detection, retaining inverse-block corrections and negative-height low-cup components. `source_cap_downward_triangular` converts the actual downward-dot serializer to upward-dot columns with a unit leading coefficient and the odd-bubble correction; `pairedExpansion_injective` retains this correction. `same_colour_source_exchange_descent` and `source_exchange_descent` conclude source descent over arbitrary permitted commutative coefficient rings, without field, grading or homogeneity assumptions. The two-odd-colour consumer `SameColourSourceFrameExamples.all_source_exchanges` and its nonempty-context full-SYM column use only the permitted axioms.

## Upward-to-oriented reduction

`SKM.nondegeneracy_of_upward_independence` in `UpwardNondegeneracyReduction.lean` combines `WeakMate.sorted_independence` with both proved contextual exchange descents. Its only independence premise is `WeakMate.UpwardIndependence cs`, at every weight over full abstract `SYM`. `nondegeneracy_iff_upward_independence` supplies the converse. No field, finite-colour, symmetrizer, grading or coefficient-homogeneity restriction is added by the reduction. The concrete two-odd-colour consumer is `UpwardNondegeneracyReductionExamples.two_odd_colour_reduction`. Both headline axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. This closes B0, not the action or upward-detection obligations needed to establish its premise. The source and target sorting notes record the checked status as well as the mathematical formulas.

## Next targets

**Actual paired target columns (checked).** `SameColourTargetFrame` attaches the complete adapted choices to finite principal columns at every local height, retaining arbitrary abstract `SYM` inputs and both boundary contexts. `positive_column` and `nonpositive_column` identify their expansions with actual postcomposition by the same-colour crossing. `PairedTargetCapColumns` constructs the normalized low-cap columns. `targetPositiveColumns_detect` and `targetNonpositiveColumns_detect` prove finite coefficient detection by the actual unit pivots, with both inverse-block and dot-slide corrections included. `SameColourTargetFrameExamples` checks positive and negative local heights in a two-colour odd datum with nonempty contexts and residual labels. Full target and source descent and B0 are now checked as described above.

`SameColourTargetFrame.pairedExpansion_injective` proves all-height independence of the actual paired sector from swapped and residual independence. Its positive-height proof uses the actual low cap outputs; its nonpositive-height proof needs only swapped independence. `plcW_comp_at` supplies composition through a propositionally equal contextual boundary. The axiom print uses only `propext`, `Classical.choice`, and `Quot.sound`.

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
