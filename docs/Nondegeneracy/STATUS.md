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
| Actual old modules and counit parity | Old quotient supercategory and representables, canonical induction-parity tensor formulas and whole counit naturality; full-CI verified in [#761](https://github.com/apellis/odd-lean/pull/761). Coefficient(1) and its moving-parity supermodule are verified in #769. Canonical induced J and categorical dotted normalization remain under verification; the odd-operator cap-sign identity is verified in #803 | `ELVOldSupermodules`, `ELVInductionParityComparison` |
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
| Weighted module descent | Modules annihilating all high-weight coefficient generators descend to the actual truncated category on the same vector spaces. Natural maps and existing isomorphisms preserve both parities and inverse products; full-CI verified in [#825](https://github.com/apellis/odd-lean/pull/825). Induction preservation and the pointwise append comparison are verified in #840; input-module naturality and generator transport remain separate | `ELVWeightedModuleDescent` |


| Arbitrary-Hom odd raw inverse | Source and corrected coordinates, leading rows, module-valued division, snake, cap pivots and both height-range input matrices are full-CI verified in [#828](https://github.com/apellis/odd-lean/pull/828). Arbitrary old endpoints, zero corners and full exterior coefficients are retained. The actual ordered crossing mate remains to be identified | `ELVOffDiagonalInputMatrix`, `ELVOffDiagonalPositiveCrossing` and their dependency chain |
| Even-moving leading boundary | Literal polynomial boundary, right-product monic bounds, recurrence and arbitrary-endpoint leading equivalence are full-CI verified in [#839](https://github.com/apellis/odd-lean/pull/839). Even division and raw input matrices remain under verification | `ELVEvenPolynomialBoundary`, `ELVEvenSRightProduct`, `ELVEvenBoundaryLeading`, `ELVEvenOffDiagonalLeading` |
| Generic module row division | Degree-shift elimination with module coefficients and invertible specified leading maps; the existing odd API is retained as corollaries. Full-CI verified in [#843](https://github.com/apellis/odd-lean/pull/843) | `DegreeShiftRowDivision` |
| Actual quotient-induction counit | The prescribed old-to-truncated induction counit is an even module isomorphism, full-CI verified in [#835](https://github.com/apellis/odd-lean/pull/835) | `ELVQuotientInduction` |
| Weighted append comparison | Old append induction preserves the full weighted coefficient annihilator, including odd generators; its descended module is canonically isomorphic to truncated append induction for each input module. Full-CI verified in [#840](https://github.com/apellis/odd-lean/pull/840). Input-module naturality and chosen generator/adjunction comparisons remain open | `ELVWeightedInduction`, `ELVAppendQuotientComparison` |
| Independent content maps and slides | Canonical append/carrier and whiskered dot foundations (#832), and distinct-colour slides (#836), are full-CI verified. The composed independently whiskered braid remains open | `ELVContentModuleAction`, `ELVContentDistinctSlides` |
| Transposed denominator units | Contentwise transpose bounds yield the prescribed squared/cross transposed norm units, without a common exponent over the weight fibre. Full-CI verified in [#811](https://github.com/apellis/odd-lean/pull/811) | `ELVTransposeDenominatorUnits` |
| Reservoir Sigma norm interface | Literal transposed source norms and target denominator units suffice for the reservoir Sigma inversion; older whole-dot nilpotence assumptions remain sufficient corollaries. Full-CI verified in [#834](https://github.com/apellis/odd-lean/pull/834), with inverse-unit mate criteria in #817. Instantiation on actual factor module categories remains open | `SwappedAssembly/Sigma/SwappingReservoir`, `Sigma/TransposeNorms`, `RouquierHomPostInverseUnits` |
| Untruncated probe modules | The old content category, its genuine all-height probe module (#831), and scalar module factorization (#842) are full-CI verified. Full ordinary quotient/action and induction comparisons remain separate | `ELVOldContentCategory`, `ELVProbeOldModule`, `ELVProbeScalarModules` |

## Remaining critical chain

1. Attach the verified arbitrary-Hom odd raw inverse (#828) to the actual
   adjunction maps. The canonical coefficient module is verified in #769;
   canonical source, cap/dot, higher-row and ordinary-source matrix comparisons
   are under verification. The decisive remaining identity is the first-row
   ordered crossing mate, followed by the parity-shifted finite module family
   and its naturality. For even moving colours, the leading boundary is
   verified in #839; division, cap pivots and both raw matrices are under
   verification. The even canonical source/counit comparison is scoped-checked
   in #859. Retain other colours' exterior coefficients throughout.
2. Finish the independent composed content braid using the verified canonical
   carriers and distinct slides (#832, #836), then build the full-ELV factor
   families and multicolour presentation comparison with `parameterTwist Sc`.
   The pointwise old/truncated append comparison is verified (#840);
   its input-module naturality, dot/crossing and chosen adjunction transport,
   and content/weight assembly remain required.
3. Instantiate the verified target denominator and transposed source-norm
   interfaces (#811, #817, #834) on compatible full-ELV factors. Complete the
   literal source-norm specialization and actual module-category universe
   instantiation. Untruncated probe module and scalar factorization are
   verified (#831, #842); exact ordinary action/induction and prescribed
   inverse-matrix comparisons remain open. Keep separate target-content
   exponents. Supply crossing coefficients and whole swapped inverse/relation
   inputs to the existing assembly.
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
