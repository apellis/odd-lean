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
| Full coefficient tensor separation | Entire bounded polynomial/exterior coefficient window remains injective after tensoring with each affine Hom, by its proved PBW freeness over the commutative ring; full-CI verified in [#812](https://github.com/apellis/odd-lean/pull/812) | `ELVCoefficientWindowTensor` |
| Joint source detection | A cutoff-independent coefficient/PBW window survives the literal coefficient and weighted-truncated cyclotomic quotients (#819). For finite colours this includes the exact `ExtendedAtMost` recovery window and jointly separates every full source Hom (#820). Both full-CI verified; no action-faithfulness premise | `ELVJointPBWDetection`, `ELVBoundedSourceDetection` |
| Affine separation | Bounded affine PBW spans inject into actual truncated quotients at cofinal cutoffs | [ELVAffineDetection](../../OddMath/QuiverHecke/CyclotomicAction/ELVAffineDetection.lean), `affinePBW_detected_at_high_cutoffs`; this theorem alone is not joint bubble/strand detection |
| Full-coefficient short columns | Prescribed balanced source, right-exact rows and commuting squares; extraction splits alpha, and alpha and Pprime are injective | [ELVCyclotomicShortColumns](../../OddMath/QuiverHecke/CyclotomicAction/ELVCyclotomicShortColumns.lean), [ELVCyclotomicAlphaCoordinates](../../OddMath/QuiverHecke/CyclotomicAction/ELVCyclotomicAlphaCoordinates.lean), `extract_comp_alpha`, `alpha_injective`, `pprime_injective` |
| Source decomposition | `sourceCoordinateEquiv` and `sourceQuotientBoundary_eq` identify the prescribed source and its induced odd polynomial row | [ELVSourceSplitting](../../OddMath/QuiverHecke/CyclotomicAction/ELVSourceSplitting.lean), [ELVSourcePolynomialQuotient](../../OddMath/QuiverHecke/CyclotomicAction/ELVSourcePolynomialQuotient.lean) |
| Crossing column | A concrete decoder splits shortCross; its range is exactly the original append crossing span | [ELVCyclotomicCrossCoordinates](../../OddMath/QuiverHecke/CyclotomicAction/ELVCyclotomicCrossCoordinates.lean), `ShortCrossCoordinates.decode_comp_shortCross`, `shortCross_injective`, `crossingEquiv` |
| Polynomial boundary | Actual corrected-row leading equivalences and division, with kernel/cokernel windows in both height ranges | [ELVBoundaryRowDivision](../../OddMath/QuiverHecke/CyclotomicAction/ELVBoundaryRowDivision.lean); these are not the categorical matrix inverse |
| Induction and vacuum comparisons | Whole comparison coherence; independent triple dot/crossing comparisons; whole-word evaluation and combined Hom crossing | `ELVContentTensorCoherence`, `ELVVacuumWordPairing` and companion content comparison modules |
| Swapped braid | All braid fields derived from inverse and coefficient inputs | `SwappedAssembly/BraidAssembly`, `crossBraidOfInputs`; concrete inputs remain to be supplied |
| Probe kernel propagation | Ordinary kernel propagation and finite-dimensional unit corollaries; integrated after full CI in [#751](https://github.com/apellis/odd-lean/pull/751) | [ProbeDotPropagation](../../OddMath/QuiverHecke/CyclotomicAction/ProbeDotPropagation.lean) |
| Actual probe corners | Literal unital End-to-corner map, exact same-colour relations, quadratic first-dot unit and second-dot injectivity; integrated after full CI in [#752](https://github.com/apellis/odd-lean/pull/752) | [ProbeWordCorner](../../OddMath/QuiverHecke/CyclotomicAction/ProbeWordCorner.lean) |
| Rectangular probe cancellation | Actual entries and support, target-corner row cancellation and distinct-kernel criterion are full-CI verified in [#756](https://github.com/apellis/odd-lean/pull/756); actual slide/quadratic unit propagation and all mixed-word dot units are now verified in #807 | [ProbeWordEntries](../../OddMath/QuiverHecke/CyclotomicAction/ProbeWordEntries.lean) |
| Cofinal first-dot probes | Cofinal binomial powers give first-dot units; same-colour quadratic relations propagate injectivity in every position, verified in [#754](https://github.com/apellis/odd-lean/pull/754). Direct monochromatic unit propagation is now verified in #768 | [ProbeWordCorner](../../OddMath/QuiverHecke/CyclotomicAction/ProbeWordCorner.lean) and companion probe modules |
| Actual content parity | Parity shifts on the existing full-ELV supernatural module categories, reusing the canonical content-module target, full-CI verified in [#755](https://github.com/apellis/odd-lean/pull/755) | [ELVContentParity](../../OddMath/QuiverHecke/CyclotomicAction/ELVContentParity.lean) |
| Actual weight categories and adjunction | Product over every content of each original weight, actual append induction and restriction, even adjunction unit/counit; full-CI verified in [#757](https://github.com/apellis/odd-lean/pull/757). Factor inverses and action relations are not supplied | [ELVWeightModules](../../OddMath/QuiverHecke/CyclotomicAction/ELVWeightModules.lean) |
| Scalar specialization | Full-ELV coefficient evaluation and exact quotient specialization, full-CI verified in [#758](https://github.com/apellis/odd-lean/pull/758). Positive-weight truncations do not specialize to nonnilpotent constants | [ELVScalarSpecialization](../../OddMath/SKM/ELVScalarSpecialization.lean) |
| Crossing-height consequences | Prescribed crossing injective at nonnegative height, surjective at nonpositive height, and an equivalence at height zero; odd moving colour and diagonal old endpoints. Full-CI verified in [#760](https://github.com/apellis/odd-lean/pull/760) | [ELVCrossingHeight](../../OddMath/QuiverHecke/CyclotomicAction/ELVCrossingHeight.lean) |
| Direct probe units | Odd/even ring-theoretic propagation and all-position cofinal monochromatic units, without finite dimension; full-CI verified in [#768](https://github.com/apellis/odd-lean/pull/768). All mixed-word positions and signed module dots are verified in #807 | [ProbeUnitPropagation](../../OddMath/QuiverHecke/CyclotomicAction/ProbeUnitPropagation.lean) |
| Actual weight dot | Normalized content induction dot assembled on actual weight E, with nilpotence at each target-content block; full-CI verified in [#772](https://github.com/apellis/odd-lean/pull/772). No common exponent over a weight fibre is asserted | [ELVWeightDot](../../OddMath/QuiverHecke/CyclotomicAction/ELVWeightDot.lean) |
| Raw append spanning | Actual append ranges are finitely spanned before coefficient truncation; full-CI verified in [#766](https://github.com/apellis/odd-lean/pull/766). Specialization and product-category dimension are separate statements | [ELVRawAppendSpanning](../../OddMath/QuiverHecke/CyclotomicAction/ELVRawAppendSpanning.lean) |
| Raw negative-height matrix | Actual crossing plus descended dotted input contractions is bijective, including height zero; full coefficients over a commutative ring, odd moving colour and diagonal old endpoints. Full-CI verified in [#777](https://github.com/apellis/odd-lean/pull/777) | [ELVNegativeCrossing](../../OddMath/QuiverHecke/CyclotomicAction/ELVNegativeCrossing.lean), `negativeCrossingEquiv`; actual snake, cap descent and recurrence are included |
| Actual old modules and counit parity | Old quotient supercategory and representables, canonical induction-parity tensor formulas and whole counit naturality; full-CI verified in [#761](https://github.com/apellis/odd-lean/pull/761). Coefficient(1), J and categorical dotted normalization remain separate; the odd-operator cap-sign identity is verified in #803 | `ELVOldSupermodules`, `ELVInductionParityComparison` |
| Arbitrary-output C0 covariance | Actual append quotient projection covariant under arbitrary old output morphisms, with full degree-dependent coefficient twist; full-CI verified in [#779](https://github.com/apellis/odd-lean/pull/779) | [ELVOffDiagonalCoefficientAction](../../OddMath/QuiverHecke/CyclotomicAction/ELVOffDiagonalCoefficientAction.lean) |
| Fixed-content module-uniform dot bound | For each target-content block, one positive exponent kills its actual normalized dot for every input module; full-CI verified in [#778](https://github.com/apellis/odd-lean/pull/778). The exponent may vary with the block; actual blockwise transpose is verified in #790 | [ELVWeightDotBounds](../../OddMath/QuiverHecke/CyclotomicAction/ELVWeightDotBounds.lean), `elvWeightDotComponent_pow_zero` |
| Scalar parity and affine Hom specialization | Actual signed Hom specialization superfunctor, retaining full coefficient parity; full-CI verified in [#762](https://github.com/apellis/odd-lean/pull/762). Cyclotomic ideal/image comparison is separate | `ELVScalarParity` and `ELVScalarHom` |

| Arbitrary-Hom long coordinates | Long extraction and section are inverse on arbitrary old source/target words, including empty Hom corners; full-CI verified in [#753](https://github.com/apellis/odd-lean/pull/753). Short-kernel, row division and categorical matrix identification remain separate | `ELVOffDiagonalLongCoordinates` |
| Denominator interface | Generic coefficient, slide, braid and supernaturality assembly uses `CrossDenominatorUnits`; the stronger whole-dot nilpotence input remains a sufficient corollary. Full-CI verified in [#767](https://github.com/apellis/odd-lean/pull/767) | `SwappedAssembly/Supernatural/CrossCoeff`, `SeparatedDenominatorInputs.md` |
| Contentwise denominator inverses | Even natural inverses assembled from the prescribed content dot bounds and a supplied homogeneous probe unit; no common weight-fibre exponent. Full-CI verified in [#794](https://github.com/apellis/odd-lean/pull/794); actual commutation and parity-shift transport verified in [#801](https://github.com/apellis/odd-lean/pull/801) | `ProductDenominatorUnits`, `ELVWeightDenominatorUnits`, `ELVShiftedDenominatorUnits` |
| Weight superadjunction | Existing weight adjunction lifted to `SKM.SuperAdjunction` with the prescribed even unit/counit; full-CI verified in [#781](https://github.com/apellis/odd-lean/pull/781). Generic even-adjunction lift exposed in [#808](https://github.com/apellis/odd-lean/pull/808) | `ELVWeightSuperAdjunction` |
| Prescribed probe action dot units | Dimension-free units at every position in mixed words; signed module, all-height including vacuum, content and weight dot isomorphisms. Full-CI verified in [#807](https://github.com/apellis/odd-lean/pull/807). No finiteness premise or full-action comparison is supplied | `ProbeAllUnits`, `ProbeSuperDotInverse`, `ProbeGlobalDotInverse`, `ProbeWeightDotInverse` |
| Binomial probe specialization | Canonical coefficients give the prescribed polynomial in both parities for arbitrary powers (#813). The actual old ideal descends to the ordinary probe ideal, preserving identities, composition and append (#814). Both full-CI verified | `ELVProbeCoefficients`, `ELVProbeSpecialization` |
| Cap-sign normalization | Prescribed scalar with exponent n(n+1)/2 cancels iterated odd-dot twists; full-CI verified in [#803](https://github.com/apellis/odd-lean/pull/803). Canonical J/counit and categorical higher-row comparison remain separate | `ELVCapSignNormalization` |

| Arbitrary-Hom exact kernel and rho | The long-extraction kernel is exactly the chronological short span, without an old-index inhabitation premise (#764). Actual rho intertwines the arbitrary-Hom section and its iterates (#785). Both full-CI verified | `ELVOffDiagonalLongKernel`, `ELVOffDiagonalRho` |
| Old induction representables | Canonical even co-Yoneda iso and arbitrary-endpoint `upperHomEquiv`, with the existing old append superfunctor; full-CI verified in [#806](https://github.com/apellis/odd-lean/pull/806). Crossing mate, cups and matrix transfer remain separate | `ELVOldInductionRepresentable`, `ELVOldAppendSuperfunctor` |
| Actual blockwise transpose | The prescribed weight-adjunction transpose dot has a contentwise exponent uniform in all target modules, retaining the odd reversal scalar; full-CI verified in [#790](https://github.com/apellis/odd-lean/pull/790) | `ELVWeightDotTranspose` |
| Mate source-unit criterion | Exact polynomial movement and source-denominator unit criterion for the existing mixed mate; full-CI verified in [#810](https://github.com/apellis/odd-lean/pull/810). Concrete transposed norms and the entire Sigma construction remain separate | `RouquierHomPostMateUnits` |
| Untruncated content specialization | Unital map from the existing old content ring to the actual all-height probe content corner, including vacuum and append; full-CI verified in [#823](https://github.com/apellis/odd-lean/pull/823). The actual module comparison is separate | `ELVProbeContentSpecialization` |
| Weighted module descent | Modules annihilating all high-weight coefficient generators descend to the actual truncated category on the same vector spaces. Natural maps and existing isomorphisms preserve both parities and inverse products; full-CI verified in [#825](https://github.com/apellis/odd-lean/pull/825). Induction preservation/comparison remains separate | `ELVWeightedModuleDescent` |

## Remaining critical chain

1. Extend the boundary and inverse from diagonal old endomorphisms to arbitrary
   old source/target words. Arbitrary-Hom long coordinates are verified in #753; the exact
   short kernel is verified in #764. Arbitrary-Hom division and matrix extensions
   remain under verification. Diagonal inverses alone
   do not imply invertibility on all representable components. Combine the
   proved prescribed source/crossing decompositions and polynomial
   boundary in the exact categorical diagram; derive the snake/
   augmented inverse at every height, including zero. Supply the required
   coefficient compatibility and naturality comparisons. The existing full-ELV
   boundary leading/division and raw inverse results cover an odd moving
   colour. An actual even-moving full-ELV inverse is still required for the
   mixed-parity action; the ordinary-polynomial global wrapper assumes its
   local inversions and does not discharge this obligation. Other colours'
   exterior coefficients cannot be treated as a commutative ground ring.
2. Construct the full-ELV factor families from that inverse and the independent
   content induction maps; finish their composed mixed braid and multicolour
   presentation comparison with algebra parameters `parameterTwist Sc`.
3. Instantiate the verified denominator interface and contentwise even natural
   inverses with compatible factor data. Probe-dot units and original-ideal
   specialization are verified; the content/module-action specialization and
   prescribed inverse-matrix comparison remain open. Use the verified blockwise adjunction transpose bound (#790), then finish
   the concrete transposed norm units and swapping-mate denominator comparison. A weight fibre
   may be infinite: retain separate target-content exponents. Supply crossing
   coefficients and whole swapped inverse/relation inputs to the existing assembly.
4. Use the verified joint source detection (#819, #820), retaining the actual
   weighted coefficient ideal, including odd generators. Construct the action's
   literal vacuum/corner evaluation and all-height normalized
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
