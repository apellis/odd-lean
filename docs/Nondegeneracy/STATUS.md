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
| Actual old modules and counit parity | Old quotient supercategory and representables, canonical induction-parity tensor formulas and whole counit naturality; full-CI verified in [#761](https://github.com/apellis/odd-lean/pull/761). Coefficient(1) and its moving-parity supermodule are verified in #769. Canonical induced J and the shifted categorical input-operator identification are verified in #838; ordinary higher-row normalization and the actual first-row mate are verified in #889; the odd-operator cap-sign identity is verified in #803 | `ELVOldSupermodules`, `ELVInductionParityComparison` |
| Arbitrary-output C0 covariance | Actual append quotient projection covariant under arbitrary old output morphisms, with full degree-dependent coefficient twist; full-CI verified in [#779](https://github.com/apellis/odd-lean/pull/779) | [ELVOffDiagonalCoefficientAction](../../OddMath/QuiverHecke/CyclotomicAction/ELVOffDiagonalCoefficientAction.lean) |
| Fixed-content module-uniform dot bound | For each target-content block, one positive exponent kills its actual normalized dot for every input module; full-CI verified in [#778](https://github.com/apellis/odd-lean/pull/778). The exponent may vary with the block; actual blockwise transpose is verified in #790 | [ELVWeightDotBounds](../../OddMath/QuiverHecke/CyclotomicAction/ELVWeightDotBounds.lean), `elvWeightDotComponent_pow_zero` |
| Scalar parity and affine Hom specialization | Actual signed Hom specialization superfunctor, retaining full coefficient parity; full-CI verified in [#762](https://github.com/apellis/odd-lean/pull/762). Cyclotomic ideal/image comparison is separate | `ELVScalarParity` and `ELVScalarHom` |

| Arbitrary-Hom long coordinates | Long extraction and section are inverse on arbitrary old source/target words, including empty Hom corners; full-CI verified in [#753](https://github.com/apellis/odd-lean/pull/753). Short-kernel, row division and categorical matrix identification remain separate | `ELVOffDiagonalLongCoordinates` |
| Denominator interface | Generic coefficient, slide, braid and supernaturality assembly uses `CrossDenominatorUnits`; the stronger whole-dot nilpotence input remains a sufficient corollary. Full-CI verified in [#767](https://github.com/apellis/odd-lean/pull/767) | `SwappedAssembly/Supernatural/CrossCoeff`, `SeparatedDenominatorInputs.md` |
| Contentwise denominator inverses | Even natural inverses assembled from the prescribed content dot bounds and a supplied homogeneous probe unit; no common weight-fibre exponent. Full-CI verified in [#794](https://github.com/apellis/odd-lean/pull/794); actual commutation and parity-shift transport verified in [#801](https://github.com/apellis/odd-lean/pull/801) | `ProductDenominatorUnits`, `ELVWeightDenominatorUnits`, `ELVShiftedDenominatorUnits` |
| Weight superadjunction | Existing weight adjunction lifted to `SKM.SuperAdjunction` with the prescribed even unit/counit; full-CI verified in [#781](https://github.com/apellis/odd-lean/pull/781). Generic even-adjunction lift exposed in [#808](https://github.com/apellis/odd-lean/pull/808) | `ELVWeightSuperAdjunction` |
| Prescribed probe action dot units | Dimension-free units at every position in mixed words; signed module, all-height including vacuum, content and weight dot isomorphisms. Full-CI verified in [#807](https://github.com/apellis/odd-lean/pull/807). No finiteness premise or full-action comparison is supplied | `ProbeAllUnits`, `ProbeSuperDotInverse`, `ProbeGlobalDotInverse`, `ProbeWeightDotInverse` |
| Binomial probe specialization | Canonical coefficients give the prescribed polynomial in both parities for arbitrary powers (#813). The actual old ideal descends to the ordinary probe ideal, preserving identities, composition and append (#814). Both full-CI verified | `ELVProbeCoefficients`, `ELVProbeSpecialization` |
| Cap-sign normalization | Prescribed scalar with exponent n(n+1)/2 cancels iterated odd-dot twists; full-CI verified in [#803](https://github.com/apellis/odd-lean/pull/803). Canonical J/counit and categorical higher-row comparison are now verified in #889 | `ELVCapSignNormalization` |

| Arbitrary-Hom exact kernel and rho | The long-extraction kernel is exactly the chronological short span, without an old-index inhabitation premise (#764). Actual rho intertwines the arbitrary-Hom section and its iterates (#785). Both full-CI verified | `ELVOffDiagonalLongKernel`, `ELVOffDiagonalRho` |
| Old induction representables | Canonical even co-Yoneda iso and arbitrary-endpoint `upperHomEquiv`, with the existing old append superfunctor; full-CI verified in [#806](https://github.com/apellis/odd-lean/pull/806). Crossing mate, cups and matrix transfer remain separate | `ELVOldInductionRepresentable`, `ELVOldAppendSuperfunctor` |
| Actual blockwise transpose | The prescribed weight-adjunction transpose dot has a contentwise exponent uniform in all target modules, retaining the odd reversal scalar; full-CI verified in [#790](https://github.com/apellis/odd-lean/pull/790) | `ELVWeightDotTranspose` |
| Mate source-unit criterion | Exact polynomial movement and source-denominator unit criterion for the existing mixed mate; full-CI verified in [#810](https://github.com/apellis/odd-lean/pull/810). Concrete transposed norms and the entire Sigma construction remain separate | `RouquierHomPostMateUnits` |
| Untruncated content specialization | Unital map from the existing old content ring to the actual all-height probe content corner, including vacuum and append; full-CI verified in [#823](https://github.com/apellis/odd-lean/pull/823). The actual module comparison is separate | `ELVProbeContentSpecialization` |
| Weighted module descent | Modules annihilating all high-weight coefficient generators descend to the actual truncated category on the same vector spaces. Natural maps and existing isomorphisms preserve both parities and inverse products; full-CI verified in [#825](https://github.com/apellis/odd-lean/pull/825). Induction preservation and the pointwise append comparison are verified in #840; input-module naturality is verified in #868; chosen generator transport remains separate | `ELVWeightedModuleDescent` |


| Arbitrary-Hom odd raw inverse | Source and corrected coordinates, leading rows, module-valued division, snake, cap pivots and both height-range input matrices are full-CI verified in [#828](https://github.com/apellis/odd-lean/pull/828). Arbitrary old endpoints, zero corners and full exterior coefficients are retained. The actual ordered crossing mate and representable matrix attachment are now verified in #889; arbitrary-module inversion remains open | `ELVOffDiagonalInputMatrix`, `ELVOffDiagonalPositiveCrossing` and their dependency chain |
| Even-moving leading boundary | Literal polynomial boundary, right-product monic bounds, recurrence and arbitrary-endpoint leading equivalence are full-CI verified in [#839](https://github.com/apellis/odd-lean/pull/839). Even division, raw input matrices and actual representable matrix attachment are now verified in #889; arbitrary-module inversion remains open | `ELVEvenPolynomialBoundary`, `ELVEvenSRightProduct`, `ELVEvenBoundaryLeading`, `ELVEvenOffDiagonalLeading` |
| Generic module row division | Degree-shift elimination with module coefficients and invertible specified leading maps; the existing odd API is retained as corollaries. Full-CI verified in [#843](https://github.com/apellis/odd-lean/pull/843) | `DegreeShiftRowDivision` |
| Actual quotient-induction counit | The prescribed old-to-truncated induction counit is an even module isomorphism, full-CI verified in [#835](https://github.com/apellis/odd-lean/pull/835) | `ELVQuotientInduction` |
| Weighted append comparison | Old append induction preserves the full weighted coefficient annihilator, including odd generators; its descended module is canonically isomorphic to truncated append induction for each input module. Full-CI verified in [#840](https://github.com/apellis/odd-lean/pull/840). Input-module naturality for every supernatural module map is verified in #868; chosen generator/adjunction comparisons remain open | `ELVWeightedInduction`, `ELVAppendQuotientComparison` |
| Independent content maps and slides | Canonical append/carrier and whiskered dot foundations (#832), and distinct-colour slides (#836), are full-CI verified. The independent prefix and suffix natural families (#901/#906) and corrected component braid (#894) are now full-CI verified and integrated; the whole corrected content relation is implemented in #933/#934 with original full CI; weight assembly remains open | `ELVContentModuleAction`, `ELVContentDistinctSlides` |
| Transposed denominator units | Contentwise transpose bounds yield the prescribed squared/cross transposed norm units, without a common exponent over the weight fibre. Full-CI verified in [#811](https://github.com/apellis/odd-lean/pull/811) | `ELVTransposeDenominatorUnits` |
| Reservoir Sigma norm interface | Literal transposed source norms and target denominator units suffice for the reservoir Sigma inversion; older whole-dot nilpotence assumptions remain sufficient corollaries. Full-CI verified in [#834](https://github.com/apellis/odd-lean/pull/834), with inverse-unit mate criteria in #817. The actual module-category universe application is verified in #861; compatible factor inputs remain open | `SwappedAssembly/Sigma/SwappingReservoir`, `Sigma/TransposeNorms`, `RouquierHomPostInverseUnits` |
| Untruncated probe modules | The old content category, its genuine all-height probe module (#831), and scalar module factorization (#842) are full-CI verified. The ordinary scalar quotient, word corners and dot units are verified in #891; chosen induction/action comparisons remain separate | `ELVOldContentCategory`, `ELVProbeOldModule`, `ELVProbeScalarModules` |


| Canonical odd source and input maps | Canonical source equivalence J and the actual shifted counit/dot agree with the raw input operators on arbitrary old Hom endpoints; their shifted matrix transfer is full-CI verified in [#838](https://github.com/apellis/odd-lean/pull/838). Ordinary higher-row normalization and the ordered crossing mate identity are now verified in #889; arbitrary-module inversion remains separate | `ELVShiftedSourceLinearEquiv`, `ELVActualCapInput`, `ELVOffDiagonalCapComparison` |
| Canonical even source and counit | Coefficient(0) is canonically ordinary restriction before induction; induced even J and its negative ordinary counit tensor formula are full-CI verified in [#859](https://github.com/apellis/odd-lean/pull/859). Raw operator attachment, the constant negative ordinary cap rows and both representable matrix transfers are now verified in #862/#889 | `ELVEvenCoefficientModule` |
| Double crossing and adjunction mate bundle | Normalized double append crossing and the actual ordinary module adjunction/mate bundle are full-CI verified in #809 and #816. The bundle's first-row tensor evaluation and actual matrix attachment are now verified in #889 | `ELVOldAppendCrossing`, `ELVOldModuleAdjunction` |
| Actual Sigma universe instance | The existing Sigma chain accepts the universe levels of the actual parity-completed module category. The exact augmented-inversion application and all affected declarations are full-CI verified in [#861](https://github.com/apellis/odd-lean/pull/861); compatible concrete factor/norm inputs are still required | `SwappedAssembly/Sigma`, `LeftwardInverse`, `Supernatural/Leftward` |
| Pairing extension and action restriction | Extend parameters and the supplied CScalars by first projection, preserve symmetrizer/homogeneity, commute with parameterTwist, and restrict every RouquierMulticolour field to the original weight group. Full-CI verified in [#864](https://github.com/apellis/odd-lean/pull/864); no concrete factor family is constructed by this restriction | `ReservoirWeightParameters` |
| Actual representable matrix inverses | The actual ordered crossing mate, literal ordinary unit/dotted cap entries and canonical parity-shifted finite coordinates give component linear equivalences for both height signs and both moving parities, including zero counts. Full-CI verified in [#889](https://github.com/apellis/odd-lean/pull/889). Arbitrary-module inversion remains open; SVec assembly and content-uniform counts are full-CI verified and integrated through #932 | `ELVActualMatrixFamilies` and its odd/even comparison chain |
| Arbitrary-module coefficient-kernel tensor | A coefficient-kernel isomorphism induces an isomorphism after balanced tensoring with any module, without flatness. Full-CI verified in [#878](https://github.com/apellis/odd-lean/pull/878). Finite kernel products and their tensor equivalence are verified in #890. The concrete kernel maps, both arbitrary-module whole-matrix identifications and explicit quotient realizations are full-CI verified and integrated in [#932](https://github.com/apellis/odd-lean/pull/932), including #911/#915/#916/#921/#923. Matching-content coefficient bijectivity and final inverse assembly remain open; actual-matrix evenness (#896) supplies the required inverse grading | `ELVKernelTensor` |
| Scalar ordinary probe category | Exact scalar ideal images, ordinary quotient category and append, literal word-corner ring equivalences and ordinary dot units are full-CI verified in [#891](https://github.com/apellis/odd-lean/pull/891). The signed ordinary induction-dot unit is verified in #893. The chosen old-to-ordinary induction comparison and quotient-inverse unit-tensor formula are verified in #897; its whole generator transport remains under verification | `ELVProbeOrdinaryCategory` and companion probe comparison modules |
| Literal source norm specialization | The literal source operators and even-moving mixed source norm are full-CI verified in [#844](https://github.com/apellis/odd-lean/pull/844). The odd-moving source norms are full-CI verified in #882. Constructed coefficients, both parity mate applications and arbitrary-intermediate-functor coefficients are in #913/#917/#925/#930; these inputs are full-CI verified and integrated through #949 | `ELVMixedSourceNorms` and companion norm modules |

## Consolidated implementations and verification boundary

The research branch is the sole persistent development line. Retired source heads
are reachable through its history and indexed in [ResearchHistory](ResearchHistory.md).
Unfinished historical source is not imported into the checked library; exact restart
points are in [HANDOFF](HANDOFF.md). History preservation establishes no theorem.

The following additions are integrated through [#949](https://github.com/apellis/odd-lean/pull/949).
Its exact source head `0cd06dc2b6978fd9b505bc0cfa343e56df05c38b` passed
[full CI](https://github.com/apellis/odd-lean/actions/runs/41395159509): changed producers
and consumers, the full build with warnings as errors, the axiom audit and all
non-vacuity checks. Original topic-head evidence below is supplemented by that
combined integration gate.

| Component | Implemented boundary | Original evidence / remaining limit |
| --- | --- | --- |
| Whole corrected content braid | Independent three-dot families, ordered polynomial evaluation and `contentMixedBraidTransform` | #933/#934 full CI; transfer to actual weight functors remains open |
| Fixed-content E/F comparisons | Fully faithful unit, supported counit, restriction/extension, nested tensor and actual inner-unit formulas | #941/#946 full CI, incorporating #909/#910/#918/#920/#924; whole generator/adjunction compatibility remains open |
| Graded coefficient tensors | Sum grading, even tensor equivalences, induction and IndRes kernel grading | #942/#905 full CI; finite kernel-product grading #907 remains a historical failed attempt |
| Mixed coefficients and mates | Both parity coefficients, parity, odd identities and raw odd dotted mate | #913/#917/#919/#922/#925/#930 full CI; raw even mate remains unfinished |
| Ordinary-right kernel endpoints | Prescribed mate source endpoint normalization | #929 full CI; matching-content coefficient bijectivity remains open |
| Off-content coefficient matrices | Actual positive and negative kernel-map bijectivity outside target content | #914/#928 verified together in #949; the earlier #928 cache-restore failure is superseded |
| Append comparison helpers | Three unit-tensor formulas, arbitrary even induction-map evaluation and chosen weighted-comparison parity | #936/#940/#938 full CI; scalar/weighted five-map specializations remain unfinished |
| Two-successor weight induction | Actual composed induction coordinates, even comparison and absent-predecessor zero cases | #945 full CI; global crossing and pair/triple relation transfer remain open |
| Last-boundary separation | Weighted separation for signed odd and ordinary even positioned last-boundary polynomials | #944 full CI; no affine reversal equivalence or identification of an action kernel is supplied |
| Diagonal positive crossing | Prescribed crossing augmented by literal low polynomial columns | #776 full CI; categorical arbitrary-module inverse is separate |

Older table rows describe their original integration boundary; the consolidated
entries above supersede older scoped-only descriptions for these components.

## Remaining critical chain

1. Complete the arbitrary-module inverse using the explicit ordinary-right
   coefficient kernels. The generic tensor mechanism and finite products
   are verified (#878/#890). Kernel maps, quotient coordinates and both
   whole forward-matrix identifications are full-CI verified and integrated
   through #932 (#911/#915/#916/#921/#923), including cofinally nonzero mixed
   exterior-coefficient consumers. Prove the matching-content coefficient
   conjugations and global pointwise bijectivity at one target-fixed count.
   Off-content vanishing and actual off-content matrix bijections (#914/#928)
   are full-CI verified and integrated through #949. Combine that bijectivity with the actual matrix evenness
   (#896); no evenness assumption on arbitrary kernels is required.
2. Complete multicolour/weight assembly with `parameterTwist Sc`. The whole
   corrected content braid and three independent dot families are implemented
   (#933/#934), with original exact-head full CI. The canonical fixed-content
   comparisons and inner-unit tensor identity are implemented (#941/#946).
   Complete unit/counit and generator compatibility, actual global crossings,
   and pair/triple whiskering transfer; two-successor induction is implemented
   (#945). The old/truncated append comparison still needs its chosen
   dot/crossing/adjunction transport, despite verified naturality and parity.
3. Assemble compatible full-ELV factors and the concrete swapped action.
   Source norms, target denominators, mate criteria, weak Sigma and actual
   category universes are verified (#811/#817/#834/#844/#861/#882).
   The ordinary probe quotient/induction comparison is verified (#891/#897),
   and its actual old-coend dot unit is verified (#927); whole generator
   transport remains open. Constructed mixed coefficients, inverse
   identities and raw odd mate applications passed original full CI
   (#913/#917/#919/#922/#925/#930) and are included in the consolidation.
   Complete the raw even mate, family identifications and remaining assembly. Use the pairing-weight extension and supplied
   CScalars transport (#864), retaining separate target-content exponents.

4. Use the verified joint source detection (#819, #820), retaining the actual
   weighted coefficient ideal, including odd generators. Construct the action's
   literal vacuum/corner evaluation and all-height normalized bubbles, prove
   the bounded recovery identity, and instantiate the existing observation
   consumer. Apply the finite-colour and upward-to-oriented reductions.

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
