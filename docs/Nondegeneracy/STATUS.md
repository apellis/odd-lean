# Odd nondegeneracy: current mathematical status

This is the authoritative current status for `research/odd-nondegeneracy`.
The proposed proof is [SwappedNondegeneracy](SwappedNondegeneracy.md); the
actionable dependency order is [HANDOFF](HANDOFF.md).
Topic notes record local arguments and their original claim boundaries;
their historical “open” lists do not override this page. Earlier inventories
and checkpoint narratives remain available in git history.

**The Phase 1 odd/mixed nondegeneracy theorem is open in Lean.** The end-to-end written
argument is proposed. Its remaining constructions can still reveal mathematical
gaps; “written proof” does not mean routine transcription.

## Scope

**Phase 1:** symmetrizable data and homogeneous admissible parameters.
**Phase 2:** after Phase 1, pursue inhomogeneous parameters while retaining
symmetrizability. **Nonsymmetrizable Cartan data are out of scope.**
The branch is complete once the odd theorem and its checked all-even
specialization match the most general cited even nondegeneracy theorems,
except for requiring 2 invertible in the base ring. The graded-coefficient
parameter benchmark and exact completion criteria are in
[FieldScopeBoundary](FieldScopeBoundary.md). Phase 2 is not yet established.

The proposed construction uses a purely even field with 2 invertible,
compatible symmetrizable Cartan superdata with positive integral symmetrizers,
homogeneous admissible parameters with separate odd-variable exponent support
and the specified leading units, and supplied `cs : CScalars Sc`.
It includes connected data, repeated colours and arbitrary colour sets.

**Ground-ring descent is already formalized.**
`SKM.nondegeneracyConjecture_of_charZeroField` in
[GroundRingNondegeneracy](../../OddMath/SKM/GroundRingNondegeneracy.lean)
reduces every ordinary commutative ring with 2 invertible to the
characteristic-zero field case for the same datum and homogeneous parameters.
It requires no domain, reducedness, flatness, finite-colour or independent-root
hypothesis on the target ring. Thus proving that field input supplies the
ordinary-ring conclusion; no additional ground-ring descent remains.
The field input is still open. This reduction retains the datum and
homogeneity conditions and does not address genuinely supercommutative
base rings or existence of CScalars for every weight realization.
Intermediate lemmas may have broader scope. The field predicate fixes the datum;
completing the present construction with a supplied positive symmetrizer
therefore establishes Phase 1. Symmetrizability is not implied by `Datum`,
homogeneous parameters or supplied normalizations, and will remain an intended
hypothesis. Relaxing parameter homogeneity belongs to Phase 2; proving the
broader nonsymmetrizable §8 conjecture is not a branch obligation.

## Established reductions and concrete inputs

“Implemented” means the named proof is present in the source; full-package
verification is a separate gate. Read each declaration for its exact hypotheses.

| Component | Implemented boundary | Source |
| --- | --- | --- |
| Arbitrary oriented boundaries | Full nondegeneracy iff upward independence at every weight; source and target exchange, including same colours, are discharged | [UpwardNondegeneracyReduction](../../OddMath/SKM/UpwardNondegeneracyReduction.lean), `nondegeneracy_iff_upward_independence` |
| Arbitrary colour sets | Finite-colour upward injectivity implies full nondegeneracy, retaining the original weight group | [FiniteColourNondegeneracy](../../OddMath/QuiverHecke/FiniteColourNondegeneracy.lean), `nondegeneracy_of_restrictColours_upward` |
| Characteristic-zero field reduction | The characteristic-zero field case for a fixed datum implies nondegeneracy over every ordinary commutative ring with 2 invertible, for homogeneous parameters and supplied CScalars; no flatness or reducedness is needed | `SKM.nondegeneracyConjecture_of_charZeroField`, `nondegeneracyConjecture_scalarChange`; imported in OddMath and exercised by `NonVacuity/GroundRingNondegeneracy`. The unresolved input is `CharZeroFieldNondegeneracy D` |
| Recovery consumer | Vacuum evaluations at all weights, word pairs and bounds imply nondegeneracy over a field | [SwappedVacuumRecovery](../../OddMath/QuiverHecke/SwappedVacuumRecovery.lean), `nondegeneracy_of_vacuum_evaluations`; evaluations remain hypotheses |
| Observation assembly | Swapped observations imply nondegeneracy, including finite-colour form | [SwappedConditionalNondegeneracy](../../OddMath/QuiverHecke/SwappedConditionalNondegeneracy.lean); concrete observations remain hypotheses |
| Probe-vacuum summand paths | Upward paths ending at zero probe content use only reservoir summands, at arbitrary word length; the finite path sum reduces to its occupied term. The canonical reservoir path is constructed for every upward labelled word and terminal reservoir content. Producers and occupied repeated-colour consumers pass strict scoped checks; full build, global axiom audit and all non-vacuity checks passed in [#1010](https://github.com/apellis/odd-lean/pull/1010) | [SwappedAssembly/VacuumPaths](../../OddMath/QuiverHecke/SwappedAssembly/VacuumPaths.lean), `SPath.subsingleton_of_upward_probe_zero`, `SPath.sum_of_upward_probe_zero`; [ReservoirPaths](../../OddMath/QuiverHecke/SwappedAssembly/ReservoirPaths.lean), `SPath.reservoirPath`. The chosen-action generator evaluation remains to be attached |
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


| Arbitrary-Hom odd raw inverse | Source and corrected coordinates, leading rows, module-valued division, snake, cap pivots and both height-range input matrices are full-CI verified in [#828](https://github.com/apellis/odd-lean/pull/828). Arbitrary old endpoints, zero corners and full exterior coefficients are retained. The actual ordered crossing mate and representable matrix attachment are now verified in #889; arbitrary-module component inverses are verified in #952; fixed-content/weight assembly remains open | `ELVOffDiagonalInputMatrix`, `ELVOffDiagonalPositiveCrossing` and their dependency chain |
| Even-moving leading boundary | Literal polynomial boundary, right-product monic bounds, recurrence and arbitrary-endpoint leading equivalence are full-CI verified in [#839](https://github.com/apellis/odd-lean/pull/839). Even division, raw input matrices and actual representable matrix attachment are now verified in #889; arbitrary-module component inverses are verified in #952; fixed-content/weight assembly remains open | `ELVEvenPolynomialBoundary`, `ELVEvenSRightProduct`, `ELVEvenBoundaryLeading`, `ELVEvenOffDiagonalLeading` |
| Generic module row division | Degree-shift elimination with module coefficients and invertible specified leading maps; the existing odd API is retained as corollaries. Full-CI verified in [#843](https://github.com/apellis/odd-lean/pull/843) | `DegreeShiftRowDivision` |
| Actual quotient-induction counit | The prescribed old-to-truncated induction counit is an even module isomorphism, full-CI verified in [#835](https://github.com/apellis/odd-lean/pull/835) | `ELVQuotientInduction` |
| Weighted append comparison | Old append induction preserves the full weighted coefficient annihilator, including odd generators; its descended module is canonically isomorphic to truncated append induction for each input module. Full-CI verified in [#840](https://github.com/apellis/odd-lean/pull/840). Input-module naturality is verified in #868; the selected tensor/unit and signed-dot formulas are full-CI verified in #963. The ordinary restriction-square and counit comparison is scoped-checked in `ELVWeightedAppendAdjunction`; crossing/inverse and content/weight transport remain open | `ELVWeightedInduction`, `ELVAppendQuotientComparison` |
| Homogeneous coefficient annihilators | Actual old E/F preserve annihilation by any homogeneous full coefficient, including the paper's even power generators; every supernatural module map commutes with even coefficients, retaining chosen inverse maps | `ELVCoefficientAnnihilation`; producer, concrete even-square/exterior consumer and all 12 owned-declaration axiom checks pass strict scoped checks; full CI verified in #972. The power-annihilated subcategory, weighted/power comparison and actual evaluation kernel remain open. [CoefficientAnnihilation](CoefficientAnnihilation.md) |
| Independent content maps and slides | Canonical append/carrier and whiskered dot foundations (#832), and distinct-colour slides (#836), are full-CI verified. The independent prefix and suffix natural families (#901/#906) and corrected component braid (#894) are now full-CI verified and integrated; the whole corrected content relation is implemented in #933/#934 with original full CI; weight assembly remains open | `ELVContentModuleAction`, `ELVContentDistinctSlides` |
| Transposed denominator units | Contentwise transpose bounds yield the prescribed squared/cross transposed norm units, without a common exponent over the weight fibre. Full-CI verified in [#811](https://github.com/apellis/odd-lean/pull/811) | `ELVTransposeDenominatorUnits` |
| Reservoir Sigma norm interface | Literal transposed source norms and target denominator units suffice for the reservoir Sigma inversion; older whole-dot nilpotence assumptions remain sufficient corollaries. Full-CI verified in [#834](https://github.com/apellis/odd-lean/pull/834), with inverse-unit mate criteria in #817. The actual module-category universe application is verified in #861; compatible factor inputs remain open | `SwappedAssembly/Sigma/SwappingReservoir`, `Sigma/TransposeNorms`, `RouquierHomPostInverseUnits` |
| Untruncated probe modules | The old content category, its genuine all-height probe module (#831), and scalar module factorization (#842) are full-CI verified. The ordinary scalar quotient, word corners and dot units are verified in #891; chosen induction/action comparisons remain separate | `ELVOldContentCategory`, `ELVProbeOldModule`, `ELVProbeScalarModules` |


| Canonical odd source and input maps | Canonical source equivalence J and the actual shifted counit/dot agree with the raw input operators on arbitrary old Hom endpoints; their shifted matrix transfer is full-CI verified in [#838](https://github.com/apellis/odd-lean/pull/838). Ordinary higher-row normalization and the ordered crossing mate identity are now verified in #889; arbitrary-module component inverses are verified in #952; fixed-content/weight assembly remains separate | `ELVShiftedSourceLinearEquiv`, `ELVActualCapInput`, `ELVOffDiagonalCapComparison` |
| Canonical even source and counit | Coefficient(0) is canonically ordinary restriction before induction; induced even J and its negative ordinary counit tensor formula are full-CI verified in [#859](https://github.com/apellis/odd-lean/pull/859). Raw operator attachment, the constant negative ordinary cap rows and both representable matrix transfers are now verified in #862/#889 | `ELVEvenCoefficientModule` |
| Double crossing and adjunction mate bundle | Normalized double append crossing and the actual ordinary module adjunction/mate bundle are full-CI verified in #809 and #816. The bundle's first-row tensor evaluation and actual matrix attachment are now verified in #889 | `ELVOldAppendCrossing`, `ELVOldModuleAdjunction` |
| Actual Sigma universe instance | The existing Sigma chain accepts the universe levels of the actual parity-completed module category. The exact augmented-inversion application and all affected declarations are full-CI verified in [#861](https://github.com/apellis/odd-lean/pull/861); compatible concrete factor/norm inputs are still required | `SwappedAssembly/Sigma`, `LeftwardInverse`, `Supernatural/Leftward` |
| Pairing extension and action restriction | Extend parameters and the supplied CScalars by first projection, preserve symmetrizer/homogeneity, commute with parameterTwist, and restrict every RouquierMulticolour field to the original weight group. Full-CI verified in [#864](https://github.com/apellis/odd-lean/pull/864); no concrete factor family is constructed by this restriction | `ReservoirWeightParameters` |
| Actual representable matrix inverses | The actual ordered crossing mate, literal ordinary unit/dotted cap entries and canonical parity-shifted finite coordinates give component linear equivalences for both height signs and both moving parities, including zero counts. Full-CI verified in [#889](https://github.com/apellis/odd-lean/pull/889). Arbitrary-module component inverses are verified in #952; fixed-content/weight assembly remains open. SVec assembly and content-uniform counts are full-CI verified and integrated through #932 | `ELVActualMatrixFamilies` and its odd/even comparison chain |
| Arbitrary-module coefficient-kernel tensor | A coefficient-kernel isomorphism induces an isomorphism after balanced tensoring with any module, without flatness. Full-CI verified in [#878](https://github.com/apellis/odd-lean/pull/878). Finite kernel products and their tensor equivalence are verified in #890. The concrete kernel maps, both arbitrary-module whole-matrix identifications and explicit quotient realizations are full-CI verified and integrated in [#932](https://github.com/apellis/odd-lean/pull/932), including #911/#915/#916/#921/#923. Target-fixed coefficient bijectivity and both prescribed arbitrary-module component inverses are full-CI verified in #951/#952; inverse parity follows from actual-matrix evenness (#896). Fixed-content/weight functor assembly remains open | `ELVKernelTensor` |
| Scalar ordinary probe category | Exact scalar ideal images, ordinary quotient category and append, literal word-corner ring equivalences and ordinary dot units are full-CI verified in [#891](https://github.com/apellis/odd-lean/pull/891). The signed ordinary induction-dot unit is verified in #893. The chosen old-to-ordinary induction comparison and quotient-inverse unit-tensor formula are verified in #897. Literal tensor/unit and signed-dot transport, and equality of scalar-descended old restriction with ordinary restriction, are scoped-checked; counit, crossing and inverse-matrix transport remain open | `ELVProbeOrdinaryCategory`, `ELVProbeAppendTensors`, `ELVProbeRestrictionComparison` and companion probe comparison modules |
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

Subsequent coordinate and inverse steps are verified in #950/#951/#952.
The exact source heads passed [coefficient-matrix CI](https://github.com/apellis/odd-lean/actions/runs/41469299353)
and [arbitrary-module inverse CI](https://github.com/apellis/odd-lean/actions/runs/41469760186),
including full build, axiom audit and all concrete consumers.

| Component | Implemented boundary | Original evidence / remaining limit |
| --- | --- | --- |
| Whole corrected content braid | Independent three-dot families, ordered polynomial evaluation and `contentMixedBraidTransform` | #933/#934 full CI; transfer to actual weight functors remains open |
| Fixed-content E/F comparisons | Fully faithful unit, supported counit, restriction/extension, nested tensor and actual inner-unit formulas | #941/#946 full CI, incorporating #909/#910/#918/#920/#924; whole generator/adjunction compatibility remains open |
| Graded coefficient tensors | Sum grading, even tensor equivalences, induction and IndRes kernel grading | #942/#905 full CI; finite kernel-product grading #907 remains a historical failed attempt |
| Mixed coefficients and mates | Both raw moving-parity dotted mates, one-sided coefficient uniqueness, inverse-first odd formula and exact earlier-coefficient comparisons | #913/#917/#919/#922/#925/#930 full CI; `ELVRawMixedEvenMate` and `ELVRawCoefficientComparison` producers, paired degree-six consumers and all 11 owned-declaration audits scoped-checked, full CI verified in #972. Concrete factor-family and CrossCoeff assembly remain open |
| Ordinary-right kernel endpoints | Prescribed mate source endpoint normalization; canonical kernel/source and finite-family coordinates, with bundled mate-row equality | #929/#950 full CI; target-fixed all-content coefficient bijectivity is verified in #951 |
| Target-fixed coefficient matrices | Positive and negative kernel maps are bijective at every old source for the target-content count, using the prescribed representable matrices and off-content zero | #951 full CI; `ELVKernelMatrixBijective` |
| Arbitrary-module matrix inverses | Prescribed unit and cap matrix isomorphisms on every old supermodule, with literal forward-map identity and even inverse, including height zero | #952 full CI; `ELVModuleMatrixInverse`; content/weight natural-functor assembly remains open |
| Whole matrix input-module naturality | Literal finite unit/cap matrices are natural in every old module map; `contentUnitMatrixFunctorNatIso` and `contentCapMatrixFunctorNatIso` give the fixed-output-content natural inverses, retaining both signs/parities, zero counts and even inverse components | Full CI passed in #961 at source head `55c6d763`; [exact-head run](https://github.com/apellis/odd-lean/actions/runs/41532403900). Chosen content E/F and original-weight assembly remain open |
| Off-content coefficient matrices | Actual positive and negative kernel-map bijectivity outside target content | #914/#928 verified together in #949; the earlier #928 cache-restore failure is superseded |
| Chosen append tensor and dot comparisons | The canonical induction-square formula on literal balanced coends identifies the selected scalar and weighted append maps on every generator and unit; both signed-dot transports are proved | Existing helpers #936/#940/#938 full CI; new `ELVInductionSquareTensors`, `ELVProbeAppendTensors`, `ELVWeightedAppendTensors` and `ELVWeightedAppendDot` producers/consumers/owned audits passed [full CI](https://github.com/apellis/odd-lean/actions/runs/41535042662) at source head `a3384f38`, integrated in #963. Weighted restriction and ordinary counit transport are scoped-checked below; scalar ordinary counit is scoped-checked below; crossing and inverse transport remain open |
| Two-successor weight induction and crossing | Composed induction coordinates, global homogeneous crossing and whole canonical pair comparison; absent-predecessor zero cases | #945 full CI; crossing and pair coherence scoped-checked, full CI verified in #972; pair/triple whiskering relations remain open |
| Distinct-colour crossing and mate | Explicit mixed PBW decoder, both outer cyclotomic quotient spans, and literal rectangular cup-crossing-cap inverse on every old representable corner | Strict scoped producers/consumers and all 208 owned-declaration axiom checks pass; full CI verified in #972. Arbitrary-module inverse and exact-content/weight transport remain open |
| Homogeneous coend square transport | The canonical map for a commuting functor square retains the literal tensor arrow and intertwines homogeneous append transformations with their full coefficient twist | `ELVInductionSquareTransform`, strict producer/mixed-quotient consumer checks and all 15 owned-declaration axiom checks pass; full CI verified in #972. Selected weighted map and two-letter crossing comparisons remain separate |
| Chosen weighted ordinary adjunction | Even identity-vector restriction-square natural isomorphism for arbitrary input-module maps, and literal ordinary counit transport through the selected append comparison | `ELVWeightedAppendAdjunction`: producer/consumer and all 26 owned declarations checked; full CI verified in #972. Normalized content/weight and crossing compatibility remain separate |
| Last-boundary separation | Weighted separation for signed odd and ordinary even positioned last-boundary polynomials | #944 full CI; no affine reversal equivalence or identification of an action kernel is supplied |
| Diagonal positive crossing | Prescribed crossing augmented by literal low polynomial columns | #776 full CI; arbitrary-module component inverses are verified in #952; fixed-content/weight assembly is separate |
| Odd exterior principal cap model | Occupied level-two model with nonzero odd exterior coefficient, signed probe square −1, homogeneous/superlinear maps and literal inverse moments K₁=−δ, K₂=1, K₃=−δ | Full-CI verified and integrated in #957. [OddCapExterior](OddCapExterior.md); this is a concrete normalization test, not the actual action attachment |
| Old vacuum coefficient extraction and signed moments | Prescribed unit-inverse rows give literal coefficient windows and full-coefficient superlinearity; the empty-word representable has zero mate source. Canonical upper-Hom transport gives the raw monomial window, actual higher cyclotomic recurrence and all-exponent signed-dot comparison | Three producers and paired mixed/exterior consumers pass strict scoped checks; all 62 owned declarations pass the axiom allowlist. full CI verified in #972. [UnitCoefficientRows](UnitCoefficientRows.md), [VacuumMoments](VacuumMoments.md), [VacuumSignedMoments](VacuumSignedMoments.md). Final power-quotient/swapped factor and mixed caps remain open |
| Coefficient-power reservoir category | The literal ideal T is contained in the coefficient annihilator; chosen old E/F, ordinary adjunction unit/counit, dots, parity shifts and both maps of supplied isomorphisms restrict with unchanged components | `ELVCoefficientPowerModules`, `ELVCoefficientPowerParity`; strict paired checks and 52 owned-declaration audits pass, full CI verified in #973. Finite-family/crossing assembly and vacuum kernel remain separate |
| Power/weight ideal sandwich and module functors | Explicit finite bound R proves W_(R+1) contained in T contained in W_N0 in the actual ELV coefficient algebra under the numerical power/cutoff bounds. Actual weighted(N0)-modules -> T-modules -> weighted(R+1)-modules retain all vector spaces and parity components | `ELVCoefficientPowers`, `ELVCoefficientPowerComparison`, `ELVCoefficientPowerSandwich`; strict paired checks and 48 owned-declaration audits pass, full CI verified in #973. Independent exterior products survive the bounded universal power quotient; actual quotient-of-quotient comparison and evaluation kernel remain open |
| Chosen old-content dot comparison | Both selected append extension and restriction comparisons intertwine the original signed dot on whole coends | `ELVContentAppendDot`, `ELVContentAppendRestrictionDot`; both parities, paired consumers and all 23 owned declarations scoped-checked, full CI verified in #973. Chosen unit/counit/crossing and matrix attachment remain open |
| Two-letter append comparison | Generic nested raw coend maps agree through both induction-composition flattenings. The chosen composed weighted append comparison has its literal quotient-tensor formula and even inverse | `ELVInductionSquareComposition`, `ELVWeightedPairAppend`; strict paired checks and 70 owned-declaration audits pass, full CI verified in #973. Selected iterated-induction, crossing and changing-content grid transport remain open |
| Chosen scalar ordinary counit | Selected append comparison, induced restriction equality, ordinary counit and scalar-value equality compose to the literal old counit on every scalar-evaluated old target module and output word | `ELVProbeCounitComparison`; strict paired mixed/vacuum checks and all 40 owned-declaration audits pass, full CI verified in #973. Normalized caps, crossing and matrix transport remain open |

| Full coefficient half-turn and bounded quotient detection | Existing contextual affine reversal and transformed-ideal identification, full total-parity composition, literal boundary-quotient equivalence and exact kernel/bounded reservoir-schedule detection for x mapped to [htCoef x] | Seven earlier producers and their 332 declarations rechecked; new homogeneous/quotient/detection and polynomial-exterior sign APIs plus occupied interior-parameter consumers scoped-checked, full CI verified in #976. Attachment to literal reservoir Hom evaluation and normalized bubbles remains open. [HalfTurnHomogeneous](HalfTurnHomogeneous.md), [HalfTurnBoundedDetection](HalfTurnBoundedDetection.md) |
| Literal coefficient power quotient | Actual A/T is algebra-isomorphic to SYM/(J+P), with both generator maps and roundtrips; its full bounded coefficient window injects. The quotient has its original parity and regular left A-module with whole T annihilation | `ELVCoefficientPowerQuotient`, `ELVCoefficientPowerGrading`; paired checks and 50 owned declarations pass. Five public forwarding declarations reuse the existing quotient grading proof, with all 56 foundation declarations audited. Full CI verified in #976. The literal old vacuum and induction-dot nilpotence are scoped-checked below; actual word/Hom evaluation remains open |
| Chosen content adjunction and E/F charts | Selected ordinary cup and whole cap squares, restriction naturality on all module maps, and chosen preceding EF/following FE natural-isomorphism charts with literal forward components | `ELVContentAppendAdjunction`, `ELVContentEFComparison`; paired mixed/odd/vacuum checks and all 69 owned declarations pass, full CI verified in #976. Signed content crossing/mate and finite parity/product inverse attachment remain open |
| Grid, iterated induction and crossings | Six-category grid flattening; chosen weighted iterated induction and prescribed equal-colour signed crossing conjugation; scalar selected iterated induction, transform and equal-colour signed crossing conjugation | Producers and paired mixed/odd/vacuum consumers scoped-checked, full CI verified in #976. Category-changing and chosen weighted ordinary mates are scoped-checked below; prescribed matrix transport remains open. [InductionGridComposition](InductionGridComposition.md), [WeightedDoubleCrossing](WeightedDoubleCrossing.md), [ProbeDoubleAppend](ProbeDoubleAppend.md) |
| Ordinary-right distinct kernels | Two-functor IndRes kernel realization, full first-factor source comparison, constructed natural coefficient-kernel inverse and ordered native-coend mate comparison | Five producers and paired mixed/exterior/shifted consumers pass strict checks and all 108 owned-declaration audits; full CI verified in #976. The arbitrary-module whole-map identity and bundled input-module inverse are now scoped-checked below; content/weight transport remains open. [DistinctMateKernel](DistinctMateKernel.md) |

| Actual distinct-mate natural inverse | The explicit all-old-module coend inverse has exactly the actual rectangular-mate forward map; the bundled inverse is natural in every old input-module map, with both maps of parity p(i)p(j) | `ELVDistinctModuleInverse`, `HomogeneousSuperfunctorIso`, `ELVDistinctModuleIso`; all producer/consumer checks and 49 new owned-declaration audits pass, full CI verified in #977. Shifted/mixed/exterior/empty consumers check both roundtrips and odd naturality. Exact-content and original-weight transport remain open |
| Literal old power vacuum and extraction | Actual fully faithful empty coefficient embedding; balanced extension of regular A/T; even A/T empty-component iso, all nonempty components zero and whole T annihilation. Prescribed inverse rows give an all-vector dot window and full coefficient Koszul law on this exact vacuum | `ELVEmptyCoefficientEmbedding`, `ELVCoefficientPowerVacuum`, `ELVCoefficientPowerRows`; strict paired checks and 116 owned audits pass, full CI verified in #977. Both independent odd coefficient vectors survive and the top-row sign is tested; no weighted replacement or cap rescaling |
| Power-category induction-dot nilpotence | For finite colours with the standing symmetrizer/homogeneous-parameter data, a positive exponent at each fixed output content kills the original signed induction dot on every literal T-annihilated module | `ELVCoefficientPowerNilpotence`; 13 owned declarations and paired consumer scoped-checked, full CI verified in #977. The consumer forces exponent greater than three on the occupied vacuum. No module finite-dimensionality assumption or uniform weight-fibre exponent |
| Exact source/power presentation in old Homs | The actual coefficient and old cyclotomic quotient kernels are the literal source relation spans; actual old scalar powers have the precise source preimage. Signed U lands in existing reversed/twisted OldCategory Homs with exact transformed kernel and explicit/reservoir bounded detection | `ELVSourceQuotientComparison`, `ELVSourcePowerComparison`, `HalfTurn/OldQuotient`; strict paired checks and 34 owned audits pass, full CI verified in #977. These are quotient-presentation kernels, not an assumed action evaluation kernel |
| Chosen mate and chart tensor transport | The chosen weighted ordinary mate square, category-changing grid mate and raw total tensor API, and selected content EF/FE chart tensor formulas retain the prescribed components | `ELVWeightedMateComparison`, `ELVInductionGridMate`, `ELVInductionGridMateTensors`, `ELVContentEFChartTensors`; strict paired checks and 97 owned audits pass, full CI verified in #977. Same-colour/content and distinct-content mate charts and finite parity/product matrix assembly remain open |

| Chosen scalar ordinary mate | The prescribed category-changing old mate is transported through the selected append/restriction maps to the given ordinary grid mate, retaining the extra minus and actual unit/counit | `ELVProbeMateComparison`; producer and mixed/vacuum consumer pass strict checks and 44 owned audits, full CI verified in #977. Normalized cap rows and prescribed matrix transport remain open |

| Literal power-vacuum higher moments | Actual inverse rows on regular A/T give the ordered monic recurrence, coefficient Koszul law and all-exponent signed/raw conversion; the complete normalized remainder series is the inverse of the reversed literal monic polynomial | `ELVCoefficientPowerMoments`, `ELVCoefficientPowerRemainders`; strict paired occupied consumers and 76 owned audits pass; full CI verified in #979. The coefficient ring remains the noncommutative A/T. Both independent odd colours have nonzero second signed moment −[δ_i]. Closed χ/δ values at the unit are scoped-checked below; arbitrary-vector and swapped cap/bubble attachment remain open |
| Weighted matrix comparison charts | Selected source and target comparison maps are linear equivalences with their exact prescribed forward maps and both inverse products | `ELVWeightedMatrixCharts`; strict paired mixed/vacuum consumer and 28 owned audits pass; full CI verified in #979. No additional invertibility premise. Complete finite matrix-entry comparison and transported inverse remain open |
| Selected dot powers and output parity | Rectangular intertwiners transport every dot power; even superspace maps retain capRowSign and the whole output parity correction. The scalar selected append/restriction comparison transports mapped dots and all powers | `ELVOperatorPowerComparison`, `ELVProbeDottedComparison`; strict paired mixed/vacuum checks and 22 owned audits pass; full CI verified in #979. Canonical normalized cap rows and full matrix attachment remain open |

| Induced power-word coordinates | Actual balanced induction of regular A/T has the chosen vacuum at the empty word and selected append-composition isomorphisms. Its coend generator h tensor 1 has kernel exactly the independent two-sided elementary-power image; signed half-turn coordinates have the transformed-ideal kernel and explicit/scheduled bounded detection | `ELVPowerWordCoordinates`, `HalfTurn/PowerWordCoordinates`; strict paired occupied two-strand/full-exterior checks and 69 owned audits pass; full CI verified through #982. This identifies source coordinates in actual word values. The signed old-module Hom/Yoneda chart, native maps and selected dot comparison are scoped-checked below; the chosen full-action evaluation remains open |
| Closed odd vacuum series | At every positive cutoff of an odd colour, actual signed even moments at the unit are the coefficients of 1/C(−z), and odd moments are (−1)^(N+1)δ times those coefficients | `ELVCoefficientPowerOddSeries`; strict occupied cutoffs-four/five consumer and 64 owned audits pass; full CI verified through #982. The exterior coefficient stays in literal A/T. Arbitrary-vector moment and native coefficient operators are scoped-checked below; the probe numerator and swapped bubble attachment remain open |
| Ordered changing-category mate degree | The prescribed double crossing and unit–negative-crossing–induced-counit mate have exactly the given crossing degree, before any invertibility assertion | `ELVInductionGridMateParity`; strict old/ordinary mixed/vacuum consumer and 3 owned audits pass; full CI verified through #982. The whole mate-family supernaturality and content matrix attachment remain separate |
| Original-weight pair dots | The independently assembled inner and outer weight dots coincide with actual single-letter content dots under the chosen supported and canonical two-step object equalities | `ELVWeightPairDots`; strict repeated-colour/vacuum consumer and 9 owned audits pass; full CI verified through #982. Crossing-square, absent-predecessor and triple relation assembly remain open |

| Old-content prescribed mate tensor square | On untruncated OldContentModules, the chosen old-content mate and the actual old matrix first entry agree through the selected EF source and restriction target charts, for all tensor coefficients | `ELVContentAppendMate`; strict mixed/inhomogeneous/height +2,0,−2 paired checks and 35 owned audits pass; full CI verified through #982. The whole module square, finite matrix inverse, coefficient truncation and original-weight transport remain separate |
| Old-content distinct mate inverse | The given positive rectangular old-content mate is pointwise bijective on every input module, with its exact forward map and raw coend inverse through both chosen charts | Four producers ending in `ELVContentDistinctMate`; strict mixed/all-odd/shifted/empty/inhomogeneous paired checks and 139 owned audits pass; full CI verified through #982. Scope is unweighted, untruncated OldContentModules. Bundled/input-natural old-content and global-truncated inverses are scoped-checked below; canonical-content and original-weight assembly remain next |
| Weighted prescribed dotted rows | Genuine selected source/target charts intertwine every ordinary unit/dot column and dot/counit row, retaining the given signed dot and exact old matrix-row maps | `ELVWeightedMatrixRows`; strict mixed/vacuum paired checks and 57 owned audits pass; full CI verified through #982. No row-equality or inverse hypothesis. Canonical finite parity coordinates and transported component inverses remain open |
| Scalar canonical cap slots | Selected scalar source maps intertwine the actual counit and every dot power; canonical parity/restriction isomorphisms are even and input-natural; each cap slot has its prescribed shifted target and literal old capMatrixEntry binding | `ELVProbeCapRowComparison`, `ELVParityRestrictionComparison`, `ELVProbeShiftedCapComparison`; strict mixed/vacuum/odd-input/old-representable paired checks and 111 owned audits pass; full CI verified through #982. The whole output parity correction and normalized kernel formula are retained. Unit-slot and whole scalar family coordinates are scoped-checked below; the complete finite inverse transport remains open |
| Power-word enriched Hom and native maps | Actual power-word module Homs have a linear Yoneda equivalence, both roundtrips and parity compatibility. Native old-arrow maps retain the full h tensor [a] twist and signed chronological convolution, and equal existing balanced induction transformations. The selected append comparison intertwines the actual dot on every vector | `ELVPowerWordYoneda`, `ELVPowerWordMorphisms`, `ELVPowerWordAppendDot`; strict occupied independent-odd/inhomogeneous/three-strand checks and 73 owned audits pass; full CI verified through #982. Selected equal/distinct crossings and arbitrary right contexts are scoped-checked below; chosen weight/swapped Hom-action evaluation remains open |
| All-vector vacuum moment and coefficient operators | On every A/T vector, the prescribed lambda/dot/unit moment map is left multiplication by its proved scalar moment. Genuine old-module coefficient algebra actions descend to A/T on every T-object and commute literally with append induction/restriction, retaining the whole-kernel source twist | `ELVCoefficientPowerMomentMaps`, `ELVCoefficientModuleMaps`, `ELVCoefficientAppendMaps`; strict occupied two-odd/inhomogeneous/mixed/append checks and 67 owned audits pass; full CI verified through #982. The vacuum-block signed probe polynomial is scoped-checked below; actual source-placed swapped bubble attachment remains open |
| Original-weight crossing linear components | The given supported crossing has its selected affine component formula; oppositely ordered crossings cancel their intermediate chart. The global component uses that same formula and is zero at an absent double predecessor | `ELVWeightPairCrossingTotals`; strict mixed/repeated/vacuum/absent-inner-predecessor checks and 6 owned audits pass; full CI verified through #982. Supported polynomial and independent dot comparisons are scoped-checked below; assemble the global quadratic and triple relation fields |

| Homogeneous content/truncated distinct inverses | Exact prescribed rectangular mates have module and input-natural inverses, retaining both inverse parities | `ELVRectangularMateIso`, `ELVContentDistinctIso`, `ELVMixedRectangularMate`, `ELVTruncatedDistinctIso`, with the global-truncated raw coend decoder; strict paired mixed/distinct-odd/shifted/empty checks pass. Canonical exact-content and original-weight transport remain open; full CI verified in #984 |
| Canonical truncated content E/F charts | Fully faithful literal content inclusion, supported extension and counit, chosen append/restriction charts, and both all-coefficient tensor formulas | Five producers ending in `ELVContentBlockAppendTensor`; strict paired canonical ContentModules consumer and 77 owned audits pass. These use the coefficient-truncated multiset content category. Its distinct inverse and original-weight assembly remain open; full CI verified in #984 |
| Prescribed grid and finite parity families | Given mate, shifted unit/dot and dot/counit entries assemble into even module maps; canonical point/family coordinates retain the prescribed gradings | `ELVParityMatrixCoordinates`, `ELVParityMatrixSquares`, `FiniteSupermoduleFamily`, `ELVInductionGridMatrixFamilies`; paired mixed/odd/zero-size checks pass. Coordinates alone do not prove matrix invertibility; full CI verified in #984 |
| Scalar source and whole family charts | Every prescribed shifted unit column and genuine E/F, F/E and value chart has its exact forward formula; whole Option/Fin source and target families have even inverse coordinates | `ELVProbeShiftedUnitComparison`, `ELVProbeMatrixCharts`, `ELVProbeMatrixFamilyCharts`; strict paired arbitrary-power/odd-input/vacuum checks pass, with 57, 52 and 65 owned audits. Both complete matrix comparison squares are scoped-checked below; inverse transport remains next; full CI verified in #984 |
| Scalar complete finite matrix squares | Every prescribed mate/unit/cap field and both whole finite matrices commute with the genuine selected source and target charts, for every finite count | `ELVProbeMatrixEntryComparison`, `ELVProbeFiniteMatrixComparison`; strict paired mixed/vacuum/all-vector checks and 53 and 22 owned audits pass. No entry-equality or invertibility premise. Transport of the given old inverses remains next; full CI verified in #984 |
| Untruncated old-content finite coordinates | Selected E/F, F/E and inclusion-value maps give whole finite shifted family equivalences, with literal forward chart and mate-tensor formulas | `ELVContentMatrixCharts`, `ELVContentGridMatrixCoordinates`; strict paired heights +2,0,−2 checks and 26 and 33 owned audits pass. Scope is explicit predecessor content i::ν in OldContentModules; absent predecessor, all entry squares and canonical truncation remain separate; full CI verified in #984 |
| Old-content all-power unit columns | The chosen following F/E and inclusion-value charts intertwine every prescribed unit/dot column with its literal old matrix field | `ELVContentMatrixRows`; strict paired arbitrary-power/mixed/inhomogeneous checks and 23 owned audits pass. Same explicit old-content predecessor scope; all unshifted fields are now scoped-checked, while shifted finite inverse assembly remains open; full CI verified in #984 |
| Weighted finite prescribed components | Ordered mate and unscaled unit/dot/counit entries give the exact canonical shifted finite module maps and degrees | `ELVWeightedMatrixComponents`; strict mixed/vacuum consumer and 83 owned audits pass. Prescribed pointwise finite inverses are scoped-checked below; fixed-content/module assembly remains open; full CI verified in #984 |
| Weighted chart and row squares | Genuine finite parity coordinates and every unshifted mate/unit/cap comparison conjugate the given old matrix isomorphisms to weighted spaces | `ELVWeightedMatrixInverse`; strict paired heights +2,0,−2 and vacuum checks and 49 owned audits pass. The prescribed forward identification and pointwise inverses are scoped-checked below; fixed-content/module assembly remains open; full CI verified in #984 |
| Signed vacuum probe polynomial | On the actual one-letter empty-source probe block, the prescribed odd induction dot satisfies (D²+1)^m=0 on the entire induced module and its supernatural-Hom precomposition action | `ELVInductionPolynomialSigns`, `ELVProbeVacuumPolynomial`, `ELVProbeOldVacuumPolynomial`; strict paired old/ordinary/parity-shifted checks pass. This is a vacuum-block relation, not a uniform last-dot relation on arbitrary contents; mixed slide and swapped attachment remain open; full CI verified in #984 |
| Occupied probe vacuum | Both selected old and ordinary append-unit vectors are nonzero at every positive probe level; at level one D²v=−v and (D²−1)v≠0 | `ELVProbeVacuumVector`, `ELVProbeVacuumUnit`; strict paired positive-level and levels-one/two checks and 31 owned audits pass. No final mixed vacuum datum is asserted; full CI verified in #984 |

| Old-content all-power cap rows | Genuine selected E/F and value charts intertwine the actual counit and every signed lower-dot power with the given old cap field | `ELVContentMatrixCaps`; strict paired mixed/inhomogeneous/heights +2,0,−2 checks and 19 owned audits pass. No chart-evenness or compatibility premise. Whole mate, finite entry assembly and absent-predecessor branch remain open; full CI verified in #986 |
| Supported weight polynomial and both independent dots | Two actual supported crossings give the original-Sc ordered polynomial under the selected pair comparison; both independently assembled weight dots intertwine through that same comparison | `ELVWeightPairQuadratic`, `ELVWeightPairDotCoordinates`; strict connected mixed/repeated-parity/all-vector consumers and 10+10 owned audits pass. The all-block quadratic components and native same-colour square are scoped-checked below; native mixed and triple field assembly remain open; full CI verified in #986 |
| Polynomial vacuum cap candidate moments | On literal A/T, λ(D²+1)^M D^(N−2M)u equals left multiplication by (−1)^(N+1)δ whenever N≥2M and N>0; at zero height this is L_(−δ) | `ELVCoefficientPowerPolynomialCap`, `ELVCoefficientPowerNonpositiveCap`; strict occupied independent-odd/inhomogeneous/zero-and-negative-height consumers and 23+5 owned audits pass. These are candidate cap operators; the prescribed mixed maps, slide and inverse-cap normalization remain open; full CI verified in #986 |

| Canonical truncated-content distinct inverse | The prescribed positive rectangular mate on ContentModules β+[j]→β+[i] is an isomorphism, both as a module map and as the whole input-natural family; its inverse has degree p(i)p(j) | Four producers ending in `ELVContentBlockDistinctInverse`; strict mixed/distinct-odd/exterior/empty/odd-input consumers and 161 owned audits pass. No extra bijectivity or flatness premise. Original-weight transport and absent-colour sectors remain separate; full CI verified in #988 |
| Whole old-content prescribed mate square | The actual mate agrees on every coend vector through the genuine selected E/F and F/E charts, with the original normalization | `ELVContentMatrixMate`; strict mixed/inhomogeneous/height +2,0,−2 checks and 19 owned audits pass. Together with unit23/cap19 this closes all unshifted relative-content fields. Shifted entries and given finite inverse attachment remain open; full CI verified in #988 |
| Prescribed weighted finite component inverses | Every first/dotted entry and both whole finite matrix squares hold; at the prescribed height signs, actual weighted components are bijective with isomorphism hom literally the given forward map, and both inverse directions even | `ELVWeightedMatrixComponents`, `ELVWeightedMatrixEntryComparison`, `ELVWeightedFiniteMatrixComparison`, `ELVWeightedMatrixComponentInverse`; strict actual-height/H0/vacuum consumers and 87+38+17+33 owned audits pass, including 83 prior declarations rechecked. Scope is global truncated input and pointwise output values. Fixed-content module and input-functor assembly remain next; full CI verified in #988 |
| Scalar inverse candidates and absent-colour old boundary | The given old inverses conjugate through the genuine content/scalar charts at i::ν. When i is absent, the global old EF source is zero, the Cartan height is nonnegative, and removing its zero principal slot gives an inverse with exactly the remaining given unit columns | `ELVProbeMatrixInverseCandidates` and three missing-colour producers; strict mixed/actual-sign/empty-output checks and 56+50 owned audits pass. The i-present scalar candidate still needs its whole forward identification; ordinary missing-colour transport is separate from this old-global boundary; full CI verified in #988 |
| Selected word crossings and arbitrary right contexts | The recursive chosen comparisons intertwine the independently given equal and distinct crossings with full-coefficient fromArrow maps, preserving the equal-colour minus. Selected append and arbitrary suffixes intertwine every old arrow, including inhomogeneous arrows | `ELVPowerWordPairCrossing`, `ELVPowerWordDistinctCrossing`, `ELVPowerWordAppendWhiskering`, `ELVPowerWordContexts`; strict occupied two-odd/contextual consumers and 42+35+11+28 owned audits pass. These compare actual source-module maps; chosen weight-action evaluation and its scheduled descent remain open; full CI verified in #988 |
| All-block weight quadratic and native generator data | The original-Sc ordered polynomial holds in the independently given weight dots on every component, including absent predecessors. Same-colour square zero is assembled as a native two-morphism equation and field of the literal RouquierData bundle | `ELVWeightQuadratic`, `ELVWeightQuadraticComponents`, `ELVWeightCrossingSquare`, `ELVRouquierData`; strict mixed/all-odd/asymmetric/absent/native-adjunction consumers and 8+2+3+8 owned audits pass. Native mixed quadratic, braid, slides and local inverse fields remain open; this is not RouquierFamily; full CI verified in #988 |
| Ground probe coordinate and extraction row | The literal height-zero probe algebra and regular empty component have their ground-scalar coordinate. The canonical full-old extension has the prescribed last inverse row to k with its exact signed-dot window on every scalar | `ELVProbeVacuumCoordinates`, `ELVProbeExtensionRows`; strict occupied levels-one/two consumers and 27+38 owned audits pass. The full-old coend has a nonzero vector with row value one. Native-content transport, parity/normalized-left-cap attachment and actual mixed slide remain separate; full CI verified in #988 |


The following successors passed the full warning-free build, global axiom
audit and every concrete consumer in #989 at source head `7ac6e4f9`
(run 41585699842), integrated at `d73f2f2f`. Their 40 producer checks and
75 exact source/consumer blobs also pass strict local checking and the
combined import. They retain all height signs, zero counts, moving parities
and full exterior coefficients.

| Interface | Established locally | Remaining scope |
| --- | --- | --- |
| Prescribed content matrix entries and inverses | `ELVContentMatrixEntries`, `ELVContentFiniteMatrixComparison`, `ELVContentGridMatrixInverse` identify both given finite maps and invert them on relative-content modules; `ELVContentGridMatrixFunctorInverse` gives input-natural inverses with literal forward maps | Canonical coefficient-truncated content and original-weight endpoint transport |
| Weighted input-natural matrix inverses | `ELVWeightedContentMatrixInverse`, `ELVWeightedMatrixFunctorInverse` bundle the prescribed finite components on canonical fixed output content, natural in arbitrary global-truncated input modules | Identify those endpoints and fields with the chosen canonical E/F composites |
| Canonical diagonal mate | `ELVContentBlockMatrixMate` compares the selected canonical-content same-colour negative mate with the ambient ordered mate through the same full source/target charts, retaining degree p(i)²=p(i) | Unit/dot and dot/counit fields through those same charts and complete inverse transport |
| Scalar prescribed matrix inverses | `ELVProbeMatrixInverse` identifies both candidate forward maps exactly; `ELVProbeMissingColourMatrix` supplies the ordinary absent-colour unit inverse, with actual unit columns | Exact normalized-left-cap row attachment and final probe/swapped use |
| Changing-content entry naturality | `ELVInductionGridMateNaturality`, `ELVInductionGridMatrixNaturality` retain input supernaturality of the prescribed mate and every matrix entry | Original-weight presentation assembly |
| Original-weight mixed boundaries and coordinates | `ELVWeightMixedMate`, `ELVContentDistinctTargets`, `ELVWeightMixedCoordinates` give the actual mixed mate degree, both absent-sector zero inverses and supported source/target identifications; `ELVWeightRectangularCross` compares the independently selected crossing through those same coordinates | Supported original-weight chosen-mate comparison and whole inverse |
| Chosen content crossing, dot and word evaluation | `ELVContentRectangularCross` compares the independently given rectangular crossing with the chosen content word crossing; `ELVPowerWordComposition`, `ELVPowerWordContent`, `ELVPowerWordWeight` identify signed source composition and all scheduled induction components; `ELVPowerWordContentDot` evaluates the chosen content dot on every source coefficient | Chosen weight dot/cross action evaluation, relation-preserving factor and recovery |
| Full-old probe parity and polynomial | `ELVProbeExtensionParity`, `ELVProbeExtensionPolynomial` attach the extraction-row parity and signed polynomial to the actual full-old extension | Native-content coefficient cap and normalized mixed slide |
| Inverse coefficient rows | `ELVContentCoefficientMaps` bundles homogeneous inverse-unit coefficient maps with surjective components and exact empty-output specialization; `ELVProbeUnitInverseRows` preserves every ordinary inverse coefficient with its canonical unshift | Identify the selected old field with the module-map API before claiming the prescribed left cap |
| Matrix heights and selected chart parity | `ELVWeightMatrixHeight` identifies both finite counts on an entire original-weight fibre, without root independence; `ELVContentComparisonParity` gives even forward/inverse maps for the selected FE charts | Assemble original-weight matrices and normalized coefficient caps through those same charts |



The following successors passed the full warning-free build, global axiom
audit and every consumer in #991 at source head `c18b8721` (run 41588533754),
integrated at `ea35e5ba`. All 11 producers, 20 exact source/consumer blobs and
277 owned declarations also pass the strict local checks and audits.

| Interface | Established locally | Remaining scope |
| --- | --- | --- |
| Native quadratic fields | `ELVWeightQuadraticRelation` proves both exact native multicolour quadratic fields in the actual independently whiskered dots and original Sc, using faithful endomorphism evaluation from `ELVEndEvaluation`; connected mixed/interior-coefficient, asymmetric odd and disconnected odd consumers pass | Native slides, braids, local inversions and complete factor assembly |
| Chosen whole weight dot | `ELVPowerWordWeightDot` evaluates the actual chosen action dot through the scheduled word comparison on every output component, including both absent and off-support sectors | Chosen whole crossing evaluation and recovery |
| Canonical all-power unit columns | `ELVFullInductionSquareRows`, `ELVContentBlockMatrixRows` compare the literal canonical-content unitDotColumn.total with the prescribed ambient column for every power through the selected full charts | Corresponding cap-row comparison and complete canonical matrix inverses |
| Scalar prescribed left row | `ELVProbeLeftCapComparison` identifies the literal old inverse coefficient module map through the selected scalar FE/value charts with every given ordinary inverse coefficient, including the exact empty-output moduleUnitCoefficient | Attach the selected native coefficient cap and normalized probe window |
| Whole original-weight distinct inverse | `ELVWeightMixedMateComparison` compares both actual chosen unit and induction of the actual counit through the same coordinates as the crossing; `ELVWeightMixedMateInverse` supplies the whole given input-natural mate inverse, both round trips and inverse degree p(i)p(j), including absent sectors | Same-colour finite matrix/local inversion assembly and complete native factor |
| Original-weight triple coordinates | `ELVWeightTripleInduction` retains all true intermediate successor blocks, canonical flattened content coordinates and both even comparison directions; actual vacuum and absent-sector consumers pass | Identify the independently chosen crossing whiskerings in these coordinates and prove native braid |
| Native coefficient caps and probe row | `ELVContentCoefficientCaps`, `ELVProbeCapMaps` construct the selected inverse-coefficient cap, with its degree and surjective components; the actual regular-probe cap is nonzero and its ground row is surjective with degree (P−1)p | Exact scalar native-cap field and normalization window, then mixed slide and final swapped assembly |



The following successors passed the full warning-free build, global axiom
audit and every concrete consumer in [#993](https://github.com/apellis/odd-lean/pull/993),
at source head `f0a2ed23af1b3344419b86bf6726586f672012ef`
([CI](https://github.com/apellis/odd-lean/actions/runs/41594069793)).

| Interface | Established locally | Remaining scope |
| --- | --- | --- |
| Native probe left-cap field and normalization | `ELVProbeLeftCapField` identifies the selected native cap with the actual ordinary inverse coefficient; `ELVProbeUnitCoefficientWindow` supplies the given-column Kronecker window; `ELVUnitDotComponents`, `ELVProbeCapWindow` give the native all-row window, actual regular-ground top extraction and the signed polynomial for the SAME native SVec dot | Input-family supernaturality, pre-Hom/parity transport, final swapped mixed slide and bubble attachment |
| Canonical counit and all dotted cap rows | `ELVFullInductionSquareCounit`, `ELVContentBlockMatrixCaps`, `ELVFullInductionSquareSourceDots`, `ELVContentBlockCapPowers` compare the actual chosen counit and EVERY literal capDotRow.total through the same full source chart, with no compatibility premise | Finite parity-coordinate assembly and complete canonical inverses |
| Same-colour weight principal and boundary | `ELVWeightMatrixBoundary` proves absent-predecessor zero EF and the required height/predecessor consequences with explicit cutoff compatibility; `ELVPiSCatRouquierMate`, `ELVWeightLocalMate` identify the GIVEN native Rouquier mate with the rectangular weight mate and its degree | Finite coordinate extraction and both native local inversion fields; FE is retained at absent predecessors |
| Chosen triple coherence | `ELVWeightTripleCoherence` identifies both pair-flattening paths with the chosen whole triple chart, including the native component formulas | Crossing whisker equations and native braid fields |
| Chosen append units and cyclicity | `ELVPowerWordContentCyclicity` extends equality at the even cyclic unit to all full-coefficient arrows; `ELVPowerWordAppendUnits` computes the literal selected weighted and content append comparisons, with a nonzero two-odd PBW-tail input and exact image | Actual chosen whole crossing evaluation and observation recovery |


The integration in [#995](https://github.com/apellis/odd-lean/pull/995) passed
the full warning-free build, global axiom audit and every concrete consumer
at source head `a51a6f9a80f5c0efbf367cc4d79a4d08f79b1f70`
([CI](https://github.com/apellis/odd-lean/actions/runs/41605147758)),
and is integrated at `8f9ad250`. Its 36 changed producers and 66 exact
producer/consumer blobs also passed strict local checks and combined imports.

| Interface | Established locally | Remaining scope |
| --- | --- | --- |
| Same-colour slides and braid on original weights | `ELVWeightNilHeckeRelation` and `ELVWeightBraid` prove the prescribed native relation fields at every module and output, including absent outputs | Mixed-colour braid fields and concrete local inverse families |
| Distinct-colour slides on original weights | `ELVWeightDistinctSlideRelations` proves both prescribed signed slide fields using the independently specified positioned dots | Mixed-colour braid fields |
| Normalized crossing, mate, unit and cap columns | Chosen normalized content/weight crossing formulas, native mate square and every unit/cap power are identified with the old grid maps | Transfer canonical local inverses and their input-supernatural entries |
| Finite local inverse adapters and canonical charts | Even finite matrix isomorphisms produce `SuperSumInvFrom`/`To` with the prescribed forwards, degrees and identities; old grid isomorphisms instantiate this. Both directions of all six canonical content charts are even and have exact component formulas | Canonical supported/absent chart transport and original-weight local inversion fields |
| Probe cap families and pre-Hom coordinates | `ELVContentCapNaturality` supplies input supernaturality; the native module window, literal cap precomposition, shifted coordinates and raw-dot Koszul powers are checked | Concrete local adjunction assembly, mixed slide and bubbles; coordinate dot and raw pre-E dot retain their proved sign difference |
| Weighted inverse row and power reservoir | The actual weighted matrix inverse gives homogeneous coefficient maps, the literal power/weighted cap comparison and full-coefficient superlinearity with nonzero odd products | Attach the chosen native inverse row and prescribed swapped bubble operators |


The local-inverse and triple-comparison integration [#997](https://github.com/apellis/odd-lean/pull/997)
passed the full warning-free build, global axiom audit and every concrete
consumer at `679df03398fa4bbff3c16f36225ec21b0b3f6ad5`
([CI](https://github.com/apellis/odd-lean/actions/runs/41607159909)), integrated
at `ce03b2b1`. Its 22 producers and 44 exact producer/consumer blobs also
passed strict local checks and combined imports.

| Interface | Established locally | Remaining scope |
| --- | --- | --- |
| Prescribed weighted local inverses on content outputs | `weightedContentLocalInverseFrom` and `weightedContentLocalInverseTo` use the proved weighted matrix isomorphisms and literal mate/unit/cap maps, with no supplied inverse premise | Transport through supported canonical charts, input-supernatural inverse-entry families and original weights |
| Canonical unit and absent predecessor | `ELVContentUnitColumnSquare` compares every unit/dot column through the selected charts; `ELVContentAbsentUnitInverse` constructs the canonical negative local inverse when the predecessor is absent, retaining FE | Supported principal chart square and natural-family assembly |
| Canonical cap row | `contentMatrixCapDotRow_square` identifies every native cap row through the full source/value charts, with both directions even | Supported principal chart square and complete local inversion transport |
| Triple crossing and dot operators | Selected first/last adjacent crossing comparisons pass through the common triple chart; the direct multicolour induction braid and all three literal native positioned-dot component formulas are checked | Three whole triple-dot chart squares and original-Sc corrected polynomial/native braid field |
| Adjacent left adjunction and probe row | `negativeLeftAdjunction` packages the existing construction from two supplied local records, their square-zero and braid relations. The raw probe row is forced by the unit window; its normalized counit sign cancels the shifted pre-Hom sign. Scalar-evaluating inputs include the occupied F(E T0) | Construct the concrete old probe local records and their required relations; no unconditional left adjunction is claimed |
| Weighted moments and polynomial cap | Actual weighted cap after every given unit/dot column equals the full-coefficient moment operator on every vector. `ELVWeightedPolynomialCaps` constructs λ·(D²+1)^M as a homogeneous module map and proves every closure, the nonpositive-height first closure and the sign-sensitive second closure on surviving odd input | Identify the prescribed mixed inverse and swapped bubble operators |


The four-pair integration [#999](https://github.com/apellis/odd-lean/pull/999)
passed the full warning-free build, global axiom audit and all concrete
consumers at `90c42b0b615babe1215beb2285e0a2dc2f2f4e3b`
([CI](https://github.com/apellis/odd-lean/actions/runs/41610482426)), integrated
at `d02c6561`. Its 124 owned declarations and eight exact producer/consumer
blobs also pass strict scoped checks and combined imports. `AugmentedInverseNaturality` derives
principal and finite auxiliary inverse-entry supernaturality from the given
forward families and pointwise local inverses, then bundles both inversion
structures. Auxiliary entries outside the finite window are canonically zero;
no inverse-naturality premise is added. `ELVGridLocalInverseFamilies` applies
these constructors to the given grid mate, unit and cap transformations;
constructed old grid natural isomorphisms instantiate its paired examples.
`ELVWeightTripleDotComparison` identifies
all three literal positioned dots through the same chosen triple chart.
`ELVWeightedCapWindows` identifies the actual weighted unit/dot cap window,
including the polynomial low window, as whole content-zero module identities
in exactly the operator form needed by `InverseCapMoments`. Concrete natural
local-inverse assembly, the corrected mixed polynomial field and the chosen
mixed cap/bubble identification remain open.


The thirteen-producer integration [#1001](https://github.com/apellis/odd-lean/pull/1001)
passed the full warning-free build, global axiom audit and all concrete
consumers at `843401347c30507d55371912f4e03ccd77e67761`
([CI](https://github.com/apellis/odd-lean/actions/runs/41615387064)), integrated
at `daffec02`. Its 354 owned declarations and 24 exact producer/consumer
blobs also passed strict local checks and combined imports.

| Interface | Established locally | Remaining scope |
| --- | --- | --- |
| Chosen content and original-weight word crossings | `ELVPowerWordContentCross` and `ELVPowerWordWeightCross` identify the prescribed crossing on the chosen word modules with the full signed old-Hom arrow operator, on every coefficient vector and all output components, including absent sectors; concrete double-E inputs with nonzero two-odd products are checked | Append/context coherence and final observation recovery |
| Absent inverse families and weight products | `ELVContentAbsentUnitFamily`, `ELVWeightAbsentUnitFamily` construct the prescribed input-supernatural inverse families at absent predecessors; the native weight pointwise/fibre inverses and arbitrary heterogeneous product assembly retain actual common height counts | Supported canonical principal square and supported block transport, then whole-weight local records |
| Old missing-colour unit matrix and modules | The given old unit matrix is conjugated through the chosen FE/value charts, with exact forward unit columns and even inverse. `ELVContentMissingUnitModules` supplies its actual even module isomorphism for all old inputs, both parities and zero cutoff | Extract/bundle the native empty-edge inverse rows and construct the adjacent local records |
| Given grid principal | `ELVInductionGridRouquierFields` identifies the actual Rouquier principal with the given negative-crossing grid mate as a whole transformation | Complete unit/cap forward fields, slides, square and braid for the concrete old local records |
| Constructed local pre-Hom adjunction | `RouquierPreAdjunction`, `ELVProbeLocalPreAdjunction` use the existing adjacent-local constructor on the prescribed probe edge and identify the constructed counit with shiftedPreCap after both Koszul factors cancel | Adjacent local records remain explicit supplied inputs; the actual evaluated mixed bend and full swapped action are separate |


[PR #1003](https://github.com/apellis/odd-lean/pull/1003) passed the
full warning-free build, global axiom audit and all concrete consumers at
`72aa0c1c` ([CI](https://github.com/apellis/odd-lean/actions/runs/41625277102)),
integrated at `41673fa3`. Its 26 producers retain the original-parameter
mixed components, full-arrow word comparisons, native matrix powers, both
absent inverse orientations, tensor vacuum and evaluated bend/row interfaces.
The module-map inverse-row names are `unitColumnModuleInverse*`; the older
vector-map `unitColumnInverse*` API is retained.

PR #1005 passed the full warning-free build, global axiom audit and all
concrete consumers at `a85d1660`
([CI](https://github.com/apellis/odd-lean/actions/runs/41626194575)), integrated
at `5695663e`. Its 22 new producers include the supported principal square,
corrected mixed braid, tensor-vacuum coordinates and cap comparisons.

The following interfaces pass strict local producer and paired consumer checks.
Read the integration boundaries above and below for the full CI gate.

| Interface | Established locally | Remaining scope |
| --- | --- | --- |
| Whole corrected mixed braid field | `ELVWeightMixedModulePolynomial`, `ELVWeightMixedBraid`, `ELVRouquierMixedBraidEquation` and `ELVWeightMixedRelation` prove the exact original-parameter chosen dotted `RouquierMulticolour.braidEq`, on every input and output including absent sectors | General multicolour braid is recorded below; assemble the complete multicolour structure and action |
| Supported canonical principal square | `ELVContentPrincipalSquare.contentPrincipalMate_square` compares the given negative-crossing grid mate through the chosen lower source and upper retarget charts, with no compatibility hypothesis, for arbitrary modules and bounds | Constructed supported/whole-weight local records are recorded below; full factor assembly remains |
| Chosen word charts and contexts | `ELVPowerWordChartParity`, `ELVPowerWordEvaluation` and `ELVPowerWordWeightContexts` give even recursive charts and actual dot/cross evaluation inside arbitrary right E-contexts and full old arrows | Full chosen Hom-action evaluation and observation recovery |
| Regular tensor-vacuum coordinates | `ELVVacuumTensorCoordinates.probeVacuumIso` is an even module isomorphism from the actual tensor vacuum at the regular probe to the original weighted vacuum, sending v tensor 1 exactly to v | Full action evaluation and prescribed swapped inverse |
| Tensor-vacuum cap and mixed polynomial | `ELVPowerVacuumContentRows`, `ELVTensorVacuumCap`, `ELVTensorVacuumPolynomialCap` and `ELVTensorVacuumPrincipalCap` identify the prescribed native inverse cap, prove the negative-height annihilation and equal-level normalization on the same occupied tensor probe | Identification with the chosen full swapped augmented inverse and bubble recovery |
| Constructed empty old local record | `ELVModuleZeroBoundary`, `ELVModuleZeroLocalInverse` and `ELVContentVacuumLocalInverse` construct the empty-edge record from the actual old induction/adjunction/dot; finite coefficient windows have no inverse or local-record premise | Adjacent one-letter record and its transported nilHecke equations |
| Old inverse and affine fields | `ELVInductionGridRouquierInverse`, `ELVOldContentRouquierInverse` attach the constructed old matrix inverses to the prescribed principal/unit/cap fields. `ELVOldContentAffineRelations` proves both signed slides and crossing square zero in the literal old quotient | Adjacent one-letter old record, followed by its normalized left adjunction |
| Constructed old left cap | `ELVProbeVacuumLocalCap` identifies the constructed empty-record cap with the prescribed regular and scalar-evaluating caps, including F(E(T0)), without a local-record premise; occupied odd components are nonzero | Adjacent-record left adjunction and full mixed inverse |

PR #1006 passed the full build, global axiom audit and every consumer at
`804dd66d` (run 41628541714), integrated at `e4374193`. Its 15 producer
successors have 30 source/consumer blobs and 404 owned-declaration audits.

| Interface | Established locally | Remaining scope |
| --- | --- | --- |
| Supported and whole-weight local inverses | `ELVContentSupportedLocalInverse`, `ELVWeightSupportedLocalInverse`, `ELVWeightLocalInverse` and `ELVWeightRouquierLocal` construct both prescribed inverse orientations, their input-natural families and the actual `SuperRouquierLoc`, including absent sectors | Full factor/presentation assembly |
| Reservoir Rouquier family | `ELVRouquierFamily.elvRouquierFamily` retains the prescribed weight products, E/F, adjunction, dots and crossings, with constructed local records. Its sole standing cutoff condition is `∀ i, (cutoff i : ℤ) = D.h i Λ`; no factor or inverse premise | Complete multicolour structure and separating swapped action |
| Exact sideways crossing | `ELVWeightCrossMate.elvActionCrossMate_isIso` identifies the presentation's four-corner `crossMate` with the constructed rectangular mate and inverts it, without a compatibility premise | Attach this field to the complete multicolour structure |
| General multicolour braid | `ELVWeightBraidPathsComparison`, `ELVWeightMulticolourBraid`, `ELVRouquierBraidEquation` and `ELVWeightBraidRelation` prove the exact uncorrected braid field for all input modules/output sectors; three distinct connected odd colours are tested | Complete multicolour assembly; the corrected field is checked separately above |
| Coefficient insertion in chosen words | `ELVPowerWordCoefficients` identifies actual full-A/T coefficient operators in literal chosen E-word values and arbitrary right contexts, retaining full parity twists, chronological product and reversal of two odd insertions | Chosen whole-Hom evaluation and observation recovery |
| Evaluated old probe category | `ELVProbeEvaluatedCategory` restricts to the full coefficient-evaluating subcategory, closed under actual old induction/restriction, parity and products. `ELVProbeEvaluatedDotUnit` constructs the entire natural signed-dot inverse on every object of that category | Canonical-content/weight gluing and complete probe family; no all-old-modules dot unit is asserted |
| Old induction composition and square | `ELVInductionGridDots` transports both given dots through flattening; `ELVInductionGridCrossSquare` proves square zero for the given negative crossing as a whole module transformation | Remaining slide transport and actual adjacent old local record |

Six further probe producers passed the full build, global axiom audit
and every concrete consumer in #1007 at `0034b2d8` (run 41630889345),
integrated at `d783c565`. Their checked source prefix `04e78b61` has 12
source/consumer blobs and 214 owned-declaration audits. Further unintegrated
source and consumer drafts are preserved in the exact history trees linked
from HANDOFF; preservation does not promote those drafts to proved results.

| Interface | Established locally | Remaining scope |
| --- | --- | --- |
| Evaluated probe adjunction | `ELVProbeEvaluatedAdjunction` retains the actual balanced unit, cap, evenness and triangles, with the literal native dot component | Global weight adjunction and local-record transport |
| Canonical old content | `ELVProbeContentReindex` and `ELVProbeCanonicalContent` transport coefficient-evaluated modules between chosen representatives, preserving physical append/restriction, dots and equal crossings | Whole weight crossing and local inverse assembly |
| Stored-target adjunction and dot inverse | `ELVProbeAppendToAdjunction` and `ELVProbeAppendToDotUnit` retain the actual maps at arbitrary stored target contents and construct their whole natural signed-dot inverse | Whole arbitrary-weight-fibre dot unit and chosen adjunction assembly |
| Probe weight E/F | `ELVProbeWeightModules` constructs actual induction/restriction on all original-weight content blocks, with a zero module at absent predecessors and full even/odd input maps | Complete probe Rouquier family and multicolour relations |

The occupied two-odd-colour consumer additionally checks both vacuum coefficient
operator orders, their minus sign on reversal, and a nonzero ordered product
after both coefficient and old cyclotomic quotients. Strict local checking
passes; see [VacuumTwoOddCoefficients](VacuumTwoOddCoefficients.md).

The integration in [#972](https://github.com/apellis/odd-lean/pull/972) passed the
[full build and audits](https://github.com/apellis/odd-lean/actions/runs/41543582786)
at source head `044a149462b8c8baf255ecc085b6470b42e5b306`, including all
393 owned declarations of the integrated batches and every concrete consumer.

The coefficient-power and selected-comparison integration in [#973](https://github.com/apellis/odd-lean/pull/973)
passed the [full build and audits](https://github.com/apellis/odd-lean/actions/runs/41546394528)
at source head `911f3e121733e08fa56aa38fd585ee04b7bc040e`, including all
233 owned declarations and every concrete consumer.

The matrix/operator integration [#982](https://github.com/apellis/odd-lean/pull/982)
passed the [full build, global axiom audit and all consumers](https://github.com/apellis/odd-lean/actions/runs/41568326406)
at source head `5d918b82ab8fb6d02ac1edf78f5c78019c815b68`.
It also integrates the source of #979/#980. The sixteen newest producers
have 488 owned declarations checked by their paired scoped audits.
The finite-family, truncated-content and probe successors passed full
[CI in #984](https://github.com/apellis/odd-lean/actions/runs/41572490013)
at source head `bf22957c00b21d697d91582b01088991aa68b4e7`, including
the full build, global axiom audit and every consumer. The weight-coordinate and cap-attachment integration #986 passed the
[full build, global axiom audit and all consumers](https://github.com/apellis/odd-lean/actions/runs/41575246618)
at `4279a451d59aa11978e410a59259690f836d59c5`. The newer mate, matrix,
context and native-relation successors above await their own full gate.

Older table rows describe their original integration boundary; the consolidated
entries above supersede older scoped-only descriptions for these components.

`ELVContentMatrixInverse` adds full-CI verified output-arrow naturality:
`contentUnitMatrixIso` and `contentCapMatrixIso` are even supermodule
isomorphisms on each fixed output-content block for every old input module.
The pointwise product families retain literal entries; inverse naturality
holds along arbitrary old arrows. The mixed consumer checks both moving
parities, a permuted output word, zero counts, inverse products and all owned
axioms. `ELVMatrixEntryNaturality` additionally gives full-CI verified input-module
naturality of all prescribed shifted entries on the whole old module
category, with additive, linear, parity-preserving summand functors. Its
mixed consumer checks the literal endpoint transports, every finite slot,
the zero-count mate and the odd third-dot Koszul sign; all owned declarations pass.
Both additions are verified by the [full build and audits](https://github.com/apellis/odd-lean/actions/runs/41489136665)
on research head `f070980ac0a0ba23b6faf79dd53faaadfce27aa2` (#953/#954).

`ELVMatrixFunctorNaturality` now assembles the whole finite-family matrices
in the input module. Its source/target functors are additive, linear and
parity preserving; the unit/cap matrices are natural in arbitrary module
maps, including odd and inhomogeneous maps. `ELVContentMatrixFunctorInverse`
uses the existing fixed-output-content isomorphisms as literal components of
`contentUnitMatrixFunctorNatIso` and `contentCapMatrixFunctorNatIso`.
The forward-map identities and even inverse components remain unchanged.
Both height signs, both moving parities and zero counts are included.
All three producers, both paired mixed-colour consumers and the audit of
all 64 owned declarations passed [full CI](https://github.com/apellis/odd-lean/actions/runs/41532403900)
at source head `55c6d763`, integrated in #961.
Compatibility with the chosen fixed-content E/F composites, their generators
and adjunction maps, and original-weight assembly remain open. See
[MatrixFunctorNaturality](MatrixFunctorNaturality.md).

`ELVRawMixedEvenMate` now proves the literal even source difference unit and
`elvRawMixedEvenMateDot_isIso` for the arbitrary-input raw coefficient.
`ELVRawCoefficientComparison` proves uniqueness from one prescribed identity,
the inverse-first odd formula, exact comparison with the earlier even/odd mate
coefficients and the parity-unified `elvRawMixedMateDot_isIso`. Strict scoped
producer/consumer checks pass for degree-six probes of both parities and a mixed
identity-functor instance whose one-strand block restricts to vacuum. Both owned
audits pass, covering eleven declarations; full CI verified in #972. These results do
not construct compatible factors or a concrete `ProbeReservoir`. See
[ELVRawMixedEvenMate](ELVRawMixedEvenMate.md) and
[ELVRawCoefficientComparison](ELVRawCoefficientComparison.md).

`SwappedVacuum/InverseCapMoments` proves the signed coefficient-window
recurrence and the height-zero principal cap identity from the literal slide,
a monic probe relation and the coefficient-extraction window. It determines
all positive-index right moments of the prescribed inverse; it assumes no
bubble-series formula. Occupied level-one and degree-two companion/nilpotent
consumers pass strict local checking and the owned-declaration axiom audit.
[Full CI](https://github.com/apellis/odd-lean/actions/runs/41522225499) passed
for source head `532683e2db4770b22950a5356863935e9c1d8851`, integrated in #955.
The coefficient-extraction window, raw monomial normalization, signed higher
moments and full-coefficient naturality are now scoped-checked on the actual
old empty-word representable in `ELVUnitCoefficientRows`, `ELVVacuumMoments`
and `ELVVacuumSignedMoments`. The final coefficient quotient, swapped factor
and mixed inverse-cap identifications remain open; this is not yet their
normalized bubble theorem. See [InverseCapMoments](InverseCapMoments.md).

`SwappedVacuum/NegativeCapMoments` proves the negative-height polynomial
cap tests: the signed slide and probe relation make the candidate cap
annihilate the mate, and monicity gives the extreme low-unit Kronecker
window. Its occupied level-two/probe-level-one consumer checks these maps
against a nontrivial whole augmented inverse, including the literal last
inverse row. Strict local checks and the audit of all eleven owned
declarations pass; [full CI](https://github.com/apellis/odd-lean/actions/runs/41523687379)
passed for source head `39301885c8edff5e07c020246ff86ad5ebd0da5a`, integrated in #956.
The general actual augmented-matrix
attachment and normalized bubble-series construction remain open.
See [NegativeCapMoments](NegativeCapMoments.md).

`ideal_eq_appendRelations_sup_outputOldRelations` in `ELVDistinctIdealSpan`
proves the full-ELV word-corner form of KKO I (9.3), with
[full CI](https://github.com/apellis/odd-lean/actions/runs/41528015864) passed
at source head `62b981b8a0c47c013e34a7c813375f166b809c67`, integrated in #958. The cyclotomic ideal in distinct final-colour
corners is exactly the sum of the two literal outer old ideals.
`cyclotomicEquiv` in `ELVDistinctCrossingQuotient` supplies the independently
balanced crossing isomorphism and the explicit inverse `q ∘ decode` on
arbitrary full-coefficient affine representatives. The ordinary right
action is retained. `moduleMate_crossing` identifies the evaluated literal
`SKM.rectangularMate` with this crossing after canonical J, which twists
the entire first tensor factor. `moduleMateEquiv_apply` attaches the
inverse on every old representable corner, including empty words and
zero cutoff. These twelve producers and both concrete mixed/exterior
consumers pass strict scoped checks; all 208 owned declarations pass the
axiom audit. full CI verified in #972. The inverse on arbitrary old modules,
exact-content and weight transport, and the full factor family remain open.
See [DistinctCrossingDecoder](DistinctCrossingDecoder.md) and
[DistinctMateComparison](DistinctMateComparison.md).

The chosen append comparisons now have literal generator formulas in
`ELVProbeAppendTensors` and `ELVWeightedAppendTensors`: the selected maps
send every old tensor to its literal quotient tensor with unchanged vector.
The canonical `ELVInductionSquareTensors` chain is evaluated on raw balanced
coends before specialization. Scalar hom/inverse parity and the scalar and
weighted signed-dot intertwining identities are included. All producers,
connected mixed/vacuum consumers and the audits of 113 owned declarations
passed [full CI](https://github.com/apellis/odd-lean/actions/runs/41535042662)
at source head `a3384f38`, integrated in #963. The scalar probe specialization
retains its documented coefficient-evaluation hypothesis, discharged by the
actual probe consumer. These results supply neither a faithful scalar
specialization nor the remaining adjunction/crossing/inverse-matrix transport.
`ELVProbeRestrictionComparison` additionally proves that old append restriction
preserves scalar coefficient evaluation and that its scalar descent equals
the prescribed ordinary restriction. The equality comparison is identity in
parity zero and zero in parity one. Its connected mixed/vacuum consumer and
audit of all 21 owned declarations pass strict local checks; full CI verified in #972.
This identifies the restriction modules, without asserting preservation of
the chosen counit or normalized caps.
See [ProbeAppendTensors](ProbeAppendTensors.md),
[ProbeRestrictionComparison](ProbeRestrictionComparison.md),
[WeightedAppendTensors](WeightedAppendTensors.md) and
[WeightedAppendDot](WeightedAppendDot.md).

`ELVWeightedAppendAdjunction` additionally supplies
the even identity-vector restriction-square natural isomorphism and the
ordinary counit comparison with the selected weighted append map. Its exact
coend formula retains the degree-zero induction component of that even
restriction comparison. The producer, paired mixed consumer and audit of all
26 owned declarations pass strict scoped checking; full CI verified in #972 for
this adjunction addition. Faithful scalar specialization, crossing/inverse
and normalized content/weight transport are not asserted.


## Remaining critical chain

1. Attach the full-CI old-module unit/cap inverses to the chosen content and
   original-weight functors. Both height signs, moving parities, zero counts,
   fixed-output-content naturality and literal forward maps are established
   (#951/#952/#961). Chosen content dot comparisons are verified in #973.
   Ordinary cup/cap compatibility and all-map EF/FE charts are now scoped-checked;
   finish canonical local inverse transport and input-supernatural inverse-entry assembly. The generic finite adapters and six even chart comparisons are now scoped-checked.
   Retain exact target-fixed counts and the absent-predecessor zero cases.
2. Complete multicolour/weight assembly with `parameterTwist Sc`. The distinct
   ideal identity, PBW quotient decoder and actual representable mate inverse
   are verified (#958/#972). Ordinary-right coefficient-kernel natural inverses
   and arbitrary-module tensor realization are scoped-checked. The actual arbitrary-module whole equality, homogeneous module inverse and
   input-module naturality passed full CI in #977. Finish exact-content/weight
   transport through the selected charts. Weight crossings/pair coherence are verified
   (#972); content braid is implemented (#933/#934). Transfer pair/triple
   remaining mixed-colour braid relations through the selected charts; same-colour braid and both distinct-colour slides are now scoped-checked. Retain the supplied
   CScalars, original weight group and balanced schedule (#864).
3. Assemble compatible factors and the swapped Hom action. Selected weighted
   restriction/counit and scalar ordinary counit are verified (#972/#973).
   Iterated weighted signed crossing, scalar grid/composite crossings and selected
   double-induction charts are scoped-checked; finish their literal mates,
   normalized caps and prescribed matrix transport. The raw moving-parity mate
   coefficients and source norms are verified; complete compatible factor and
   CrossCoeff fields without a uniform exponent over weight fibres.
4. Finish the literal power-reservoir vacuum and observations. The T-annihilated
   category and numerical weighted/power bridge are verified (#973). Actual
   A/T presentation, the literal old regular vacuum and its inverse-row window
   are scoped-checked. Induction-dot nilpotence now follows through the proved
   weighted comparison at each formal content; no module dimension premise is
   used. Actual higher moments and their noncommutative inverse series are now scoped-checked.
   Closed χ/δ values at the unit are scoped-checked; attach their arbitrary-vector
   operator identities and the prescribed swapped caps/bubbles. The
   exact source/power kernels and signed half-turn detection in literal old Homs
   are scoped-checked. Actual iterated vacuum word values, transformed coordinate kernels, signed
   old-module Hom/Yoneda maps and selected dot comparisons are scoped-checked.
   Finish the selected pair crossing and compare with the chosen swapped
   Hom action on full coefficient vectors. Prove
   normalized bubble coefficients and bounded recovery for each requested weight,
   word pair and degree bound, then instantiate the
   observation, finite-colour and upward-to-oriented reductions.

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
