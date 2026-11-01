# Odd nondegeneracy: current mathematical status

This is the authoritative current status for `research/odd-nondegeneracy`.
The proposed proof is [SwappedNondegeneracy](SwappedNondegeneracy.md); the
actionable dependency order is [HANDOFF](HANDOFF.md).
Topic notes record local arguments and their original claim boundaries;
their historical “open” lists do not override this page. Earlier inventories
and checkpoint narratives remain available in git history.

**Full odd/mixed nondegeneracy is open in Lean.** The end-to-end written
argument is proposed. Its remaining constructions can still reveal mathematical
gaps; “written proof” does not mean routine transcription.

## Scope

The proposed theorem uses a purely even field with 2 invertible, compatible
symmetrizable Cartan superdata with positive integral symmetrizers, homogeneous
admissible parameters with separate odd-variable exponent support and the
specified leading units, and supplied `cs : CScalars Sc`.
It includes connected data, repeated colours and arbitrary colour sets.
It does not assert arbitrary-ground-ring nondegeneracy or existence of
CScalars for every weight realization. Intermediate lemmas may have broader scope.

## Established reductions and concrete inputs

“Implemented” means the named proof is present in the source; full-package
verification is a separate gate. Read each declaration for its exact hypotheses.

| Component | Implemented boundary | Source |
| --- | --- | --- |
| Arbitrary oriented boundaries | Full nondegeneracy iff upward independence at every weight; source and target exchange, including same colours, are discharged | [UpwardNondegeneracyReduction](../../OddMath/SKM/UpwardNondegeneracyReduction.lean), `nondegeneracy_iff_upward_independence` |
| Arbitrary colour sets | Finite-colour upward injectivity implies full nondegeneracy, retaining the original weight group | [FiniteColourNondegeneracy](../../OddMath/QuiverHecke/FiniteColourNondegeneracy.lean), `nondegeneracy_of_restrictColours_upward` |
| Recovery consumer | Vacuum evaluations at all weights, word pairs and bounds imply nondegeneracy over a field | [SwappedVacuumRecovery](../../OddMath/QuiverHecke/SwappedVacuumRecovery.lean), `nondegeneracy_of_vacuum_evaluations`; evaluations remain hypotheses |
| Observation assembly | Swapped observations imply nondegeneracy, including finite-colour form | [SwappedConditionalNondegeneracy](../../OddMath/QuiverHecke/SwappedConditionalNondegeneracy.lean); concrete observations remain hypotheses |
| Affine separation | Bounded affine PBW spans inject into actual truncated quotients at cofinal cutoffs | [ELVAffineDetection](../../OddMath/QuiverHecke/CyclotomicAction/ELVAffineDetection.lean), `affinePBW_detected_at_high_cutoffs`; this theorem alone is not joint bubble/strand detection |
| Full-coefficient short columns | Prescribed balanced source, right-exact rows and commuting squares; extraction splits alpha, and alpha and Pprime are injective | [ELVCyclotomicShortColumns](../../OddMath/QuiverHecke/CyclotomicAction/ELVCyclotomicShortColumns.lean), [ELVCyclotomicAlphaCoordinates](../../OddMath/QuiverHecke/CyclotomicAction/ELVCyclotomicAlphaCoordinates.lean), `extract_comp_alpha`, `alpha_injective`, `pprime_injective` |
| Source decomposition | `sourceCoordinateEquiv` and `sourceQuotientBoundary_eq` identify the prescribed source and its induced odd polynomial row | [ELVSourceSplitting](../../OddMath/QuiverHecke/CyclotomicAction/ELVSourceSplitting.lean), [ELVSourcePolynomialQuotient](../../OddMath/QuiverHecke/CyclotomicAction/ELVSourcePolynomialQuotient.lean) |
| Crossing column | A concrete decoder splits shortCross; its range is exactly the original append crossing span | [ELVCyclotomicCrossCoordinates](../../OddMath/QuiverHecke/CyclotomicAction/ELVCyclotomicCrossCoordinates.lean), `ShortCrossCoordinates.decode_comp_shortCross`, `shortCross_injective`, `crossingEquiv` |
| Polynomial boundary | Actual corrected-row leading equivalences and division, with kernel/cokernel windows in both height ranges | [ELVBoundaryRowDivision](../../OddMath/QuiverHecke/CyclotomicAction/ELVBoundaryRowDivision.lean); these are not the categorical matrix inverse |
| Induction and vacuum comparisons | Whole comparison coherence; independent triple dot/crossing comparisons; whole-word evaluation and combined Hom crossing | `ELVContentTensorCoherence`, `ELVVacuumWordPairing` and companion content comparison modules |
| Swapped braid | All braid fields derived from inverse and coefficient inputs | `SwappedAssembly/BraidAssembly`, `crossBraidOfInputs`; concrete inputs remain to be supplied |
| Probe kernel propagation | Ordinary kernel propagation and finite-dimensional unit corollaries; integrated after full CI in [#751](https://github.com/apellis/odd-lean/pull/751) | [ProbeDotPropagation](../../OddMath/QuiverHecke/CyclotomicAction/ProbeDotPropagation.lean) |
| Actual probe corners | Literal unital End-to-corner map, exact same-colour relations, quadratic first-dot unit and second-dot injectivity; integrated after full CI in [#752](https://github.com/apellis/odd-lean/pull/752) | [ProbeWordCorner](../../OddMath/QuiverHecke/CyclotomicAction/ProbeWordCorner.lean) |
| Rectangular probe cancellation | Actual entries and support, target-corner row cancellation and distinct-kernel criterion are full-CI verified in [#756](https://github.com/apellis/odd-lean/pull/756); actual slide/quadratic unit propagation remains separate | [ProbeWordEntries](../../OddMath/QuiverHecke/CyclotomicAction/ProbeWordEntries.lean) |
| Cofinal first-dot probes | Cofinal binomial powers give first-dot units; same-colour quadratic relations propagate injectivity in every position, verified in [#754](https://github.com/apellis/odd-lean/pull/754). Direct monochromatic unit propagation is now verified in #768 | [ProbeWordCorner](../../OddMath/QuiverHecke/CyclotomicAction/ProbeWordCorner.lean) and companion probe modules |
| Actual content parity | Parity shifts on the existing full-ELV supernatural module categories, reusing the canonical content-module target, full-CI verified in [#755](https://github.com/apellis/odd-lean/pull/755) | [ELVContentParity](../../OddMath/QuiverHecke/CyclotomicAction/ELVContentParity.lean) |
| Actual weight categories and adjunction | Product over every content of each original weight, actual append induction and restriction, even adjunction unit/counit; full-CI verified in [#757](https://github.com/apellis/odd-lean/pull/757). Factor inverses and action relations are not supplied | [ELVWeightModules](../../OddMath/QuiverHecke/CyclotomicAction/ELVWeightModules.lean) |
| Scalar specialization | Full-ELV coefficient evaluation and exact quotient specialization, full-CI verified in [#758](https://github.com/apellis/odd-lean/pull/758). Positive-weight truncations do not specialize to nonnilpotent constants | [ELVScalarSpecialization](../../OddMath/SKM/ELVScalarSpecialization.lean) |
| Crossing-height consequences | Prescribed crossing injective at nonnegative height, surjective at nonpositive height, and an equivalence at height zero; odd moving colour and diagonal old endpoints. Full-CI verified in [#760](https://github.com/apellis/odd-lean/pull/760) | [ELVCrossingHeight](../../OddMath/QuiverHecke/CyclotomicAction/ELVCrossingHeight.lean) |
| Direct probe units | Odd/even ring-theoretic propagation and all-position cofinal monochromatic units, without finite dimension; full-CI verified in [#768](https://github.com/apellis/odd-lean/pull/768). Mixed-word propagation is under verification | [ProbeUnitPropagation](../../OddMath/QuiverHecke/CyclotomicAction/ProbeUnitPropagation.lean) |
| Actual weight dot | Normalized content induction dot assembled on actual weight E, with nilpotence at each target-content block; full-CI verified in [#772](https://github.com/apellis/odd-lean/pull/772). No common exponent over a weight fibre is asserted | [ELVWeightDot](../../OddMath/QuiverHecke/CyclotomicAction/ELVWeightDot.lean) |
| Raw append spanning | Actual append ranges are finitely spanned before coefficient truncation; full-CI verified in [#766](https://github.com/apellis/odd-lean/pull/766). Specialization and product-category dimension are separate statements | [ELVRawAppendSpanning](../../OddMath/QuiverHecke/CyclotomicAction/ELVRawAppendSpanning.lean) |

## Remaining critical chain

1. Extend the boundary and inverse from diagonal old endomorphisms to arbitrary
   old source/target words. Arbitrary-Hom long coordinates and the exact
   short-kernel construction are under verification; diagonal inverses alone
   do not imply invertibility on all representable components. Combine the
   proved prescribed source/crossing decompositions and polynomial
   boundary in the exact categorical diagram; derive the snake/
   augmented inverse at every height, including zero. Supply the required
   coefficient compatibility, naturality and integer-degree comparisons.
2. Construct the full-ELV factor families from that inverse and the independent
   content induction maps; finish their composed mixed braid and multicolour
   presentation comparison with algebra parameters `parameterTwist Sc`.
3. Repair the denominator interface at the correct quantifier: actual postdots
   are nilpotent separately on each target-content block. A weight fibre can
   be infinite, so no uniform exponent on its entire product is available.
   Componentwise denominator units and their even natural inverses are under
   verification; the older whole-endomorphism nilpotence constructor is only
   a sufficient special case. Supply concrete probe/reservoir data, crossing
   coefficients and whole swapped
   inverse/relation inputs. Existing conditional assembly then yields the action.
4. Construct its literal vacuum/corner evaluation and all-height normalized
   bubbles, prove the bounded recovery identity, and instantiate the existing
   observation consumer. Apply the already implemented finite-colour and
   upward-to-oriented reductions.

The older `GlobalFactorNondegeneracy.globalProbeReservoir` accepts
`I → Polynomial k` parameters and conditional local inversions. It is not a
construction of the full exterior-coefficient reservoir. A compatible
full-ELV family construction is a prerequisite for final synthesis.

## Verification

The initial reviewed snapshot was e522e775; its cancelled build is not a
verification claim. Subsequent integrations use their own exact-head CI.
The latest integrated mathematical additions above passed full build with
warnings as errors, axiom audit and concrete non-vacuity consumers before
merge. Topic branches and proposed source are not established by submission
alone. Finite Python models are evidence about their instances, not proofs of
the general action or conjecture.
