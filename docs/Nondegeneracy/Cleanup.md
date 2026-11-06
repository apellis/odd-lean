# Cleanup of `research/odd-nondegeneracy` before merging into `master`

This note records the simplification of the research branch: what is retained, how
unused code was identified, what was removed, and what remains to be done before the
branch is merged into `master`. It is kept current as the cleanup proceeds.

## What is retained

* Every module and non-vacuity check present on `master` (published-result
  formalization).
* The Phase 1 theorem `QuiverHecke.nondegeneracy_of_symmetrizer` (BE2, arXiv:1701.04133v2,
  §8) with its hypotheses unchanged, and everything it uses.
* The consequences `QuiverHecke.SerreComplex.decategorification` and
  `decategorificationEquiv` (BE2 §12), the Hom bases and graded dimensions
  ([HomBases](HomBases.md)), and the Phase 2 modules (`SKM.GradedParameters`,
  `SKM.LowerDegreeParameters`, `SKM.TruncatedReesParameters`, `SKM.SymComponentBasis`,
  `QuiverHecke.Grading`).
* The non-vacuity checks of these results: those on `master`, `Decategorification`,
  `GroundRingNondegeneracy`, `HomBases`, `SwappedRouteNondegeneracy`,
  `VacuumRouteEvenComparison` and the Phase 2 checks.
* Everything imported by an open pull request against this branch.

## Method

Import closure alone is too coarse: the module of the Phase 1 theorem imports 1853
modules (362k lines). Instead the declaration-level dependency graph was computed from
the compiled `.olean` files: for every declaration, the declarations its type and value
use. A module is *live* if it is one of the retained modules above or contains a
declaration reachable from the retained theorems, from the declarations of retained
modules, or from an identifier occurring in a retained non-vacuity check. All other
modules are unused by any retained result and are removed; a retained module that
imported a removed module imports that module's own imports instead. CI (full build,
axiom audit and the non-vacuity library) is the check that nothing retained depended on
a removed module.

A module is removed only if no declaration of any retained module, used or not, refers
to it, so that retained modules compile unchanged.

Unused declarations inside the remaining research modules were then removed with the
graph of the reduced tree. A theorem or definition is removed only if no retained
theorem and no declaration of a retained module depends on it, and its name occurs in no
non-vacuity file, documentation note or remaining Lean code (outside comments). Structures,
instances, examples and declarations carrying an attribute are kept, and the removal is
closed under dependencies. Modules left without declarations were then removed in the
same way as unused modules, unless a retained declaration still refers to them.

## Sizes

| | `OddMath` modules | lines | non-vacuity files | lines |
|---|---|---|---|---|
| research tip before cleanup | 3109 | 644,846 | 1383 | 116,479 |
| after removing unused modules | 2929 | 621,573 | 103 | 4,620 |
| after removing unused declarations (1983) and empty modules (25) | 2904 | 596,582 | 104 | 4,726 |
| later research PRs, then removing 20 unreached modules | 2895 | 596,756 | 108 | 4,882 |
| later research PRs | 2907 | 598,511 | 119 | 5,841 |
| second pass: removing unused declarations (909) and empty modules (9) | 2898 | 584,933 | 119 | 5,841 |
| `master` | 1321 | | 90 | |

The Phase 1 theorem alone uses declarations from 1584 modules; the remaining research
modules after this step are kept because a retained result uses one of their
declarations or a declaration of a retained module refers to them.

## Removed modules

180 `OddMath` modules (23,316 lines) contribute no declaration to
any retained result: earlier routes (cyclotomic-action content and append constructions,
earlier Rouquier mate and inverse constructions, earlier swapped-assembly variants) and
their example files. 1280 research non-vacuity files (111,859 lines)
exercised intermediate lemmas only and are removed with them. Git history keeps all of them.

<details><summary>Removed `OddMath` modules (lines)</summary>

| module | lines |
|---|---|
| `OddMath/Algebra/FrobeniusResolvent.lean` | 78 |
| `OddMath/Diagrams/OddNilHecke/CyclotomicExteriorObstruction.lean` | 67 |
| `OddMath/Diagrams/OddNilHecke/CyclotomicNorm.lean` | 71 |
| `OddMath/Diagrams/OddNilHecke/SeparatedCrossing.lean` | 62 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendContentBoundary.lean` | 165 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendContentCrossingImage.lean` | 210 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendContentShortFactor.lean` | 138 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendContentShortImage.lean` | 215 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendTensorCoordinates.lean` | 110 |
| `OddMath/QuiverHecke/CyclotomicAction/Comparison.lean` | 54 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAffineDetection.lean` | 123 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAppendKernel.lean` | 132 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAppendPolynomialIdempotents.lean` | 105 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAppendProjective.lean` | 129 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAppendRowsEquivalence.lean` | 378 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAppendSupport.lean` | 61 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVBoundaryRowDivision.lean` | 262 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVBoundaryRowSplitting.lean` | 299 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVBoundarySnake.lean` | 171 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVBoundedSourceDetection.lean` | 107 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVCoefficientAppendMaps.lean` | 105 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVCoefficientPowerNilpotence.lean` | 146 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVCoefficientPowerParity.lean` | 77 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVCoefficientWindowTensor.lean` | 101 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentAbsentUnitFamily.lean` | 53 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentAssociativityTensor.lean` | 52 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentBlockMatrixCaps.lean` | 39 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentBlockMatrixCharts.lean` | 128 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentBraidTransforms.lean` | 173 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentCastCoherence.lean` | 66 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentCrossingTransforms.lean` | 88 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentDotTransforms.lean` | 144 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentExactness.lean` | 152 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentGridMatrixFunctorInverse.lean` | 121 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentMatrixComponents.lean` | 181 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentMissingLocal.lean` | 39 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentMissingUnitNaturality.lean` | 50 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentMixedBraidTransforms.lean` | 184 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentModuleBound.lean` | 66 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentPairOuterTensor.lean` | 114 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentTripleDots.lean` | 272 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentTripleTensor.lean` | 74 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentVacuumCoefficients.lean` | 48 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentVacuumLocalInverse.lean` | 38 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentWhiskeredMixedBraid.lean` | 141 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVCrossingHeight.lean` | 103 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVDistinctModuleIso.lean` | 111 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVGradedKernelEquivalence.lean` | 57 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVIndResKernelNaturality.lean` | 112 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVInductionAssociativity.lean` | 108 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVInductionGridMatrixFunctor.lean` | 239 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVInductionKernelGrading.lean` | 85 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVInductionSquareComposition.lean` | 110 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVInductionUnitNaturality.lean` | 41 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVJointPBWDetection.lean` | 117 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVMixedCoefficientParity.lean` | 103 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVMixedEvenMateInversion.lean` | 107 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVMixedMateInversion.lean` | 138 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVMixedOddCoefficientIdentities.lean` | 99 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVMixedRectangularMate.lean` | 43 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVModuleCentreDegree.lean` | 63 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVModuleNilpotence.lean` | 71 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVModuleZeroLocalInverse.lean` | 115 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVMovingNormRegularity.lean` | 125 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVNegativeCrossing.lean` | 294 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVOldContentBraid.lean` | 46 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVOldContentRouquierInverse.lean` | 43 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVOldCorrectedInductionBraid.lean` | 108 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVOldCorrectedNestedBraid.lean` | 213 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVOldInductionBraid.lean` | 42 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVOldMateTensors.lean` | 67 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVOldNestedBraid.lean` | 86 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVOldNestedMulticolourBraid.lean` | 181 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVOldPolynomialTransport.lean` | 66 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVPositiveCrossing.lean` | 118 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVPowerWordDistinctCrossing.lean` | 325 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeCoefficientCapUniqueness.lean` | 92 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeCoefficientExpansion.lean` | 155 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeCounitComparison.lean` | 216 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeDoubleCrossing.lean` | 60 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeEvaluatedBraid.lean` | 80 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeExtensionParity.lean` | 100 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeExtensionPolynomial.lean` | 86 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeExtensionRows.lean` | 94 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeFiniteMatrixComparison.lean` | 104 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeMatrixEntryComparison.lean` | 344 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeMatrixFamilyCharts.lean` | 229 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeMatrixInverse.lean` | 195 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeMatrixInverseCandidates.lean` | 115 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeOldDotUnit.lean` | 104 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeSeparatedBends.lean` | 180 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeVacuumLocalCap.lean` | 148 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeWeightTripleCoordinates.lean` | 69 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVQPDivisionEquiv.lean` | 294 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVQuotientPresheaf.lean` | 160 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVRawAppendSpanning.lean` | 134 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVRawCoefficientComparison.lean` | 138 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVRawMixedCoefficient.lean` | 205 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVRawMixedEvenMate.lean` | 129 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVRawMixedMate.lean` | 88 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVRestrictionMatrixCharts.lean` | 77 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVSourceProjective.lean` | 158 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVSourceRowsEquivalence.lean` | 356 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVTensorEvenVacuumCap.lean` | 126 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVTensorHomEntries.lean` | 111 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVTensorVacuumCapInverseAttach.lean` | 114 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVTensorVacuumPolynomialCap.lean` | 94 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVTensorVacuumPolynomialWindow.lean` | 85 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVTensorVacuumPrincipalCap.lean` | 105 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVTensorVacuumPrincipalFactor.lean` | 71 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVTensorWordQuotientObservation.lean` | 93 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVTruncatedDetection.lean` | 267 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVTruncatedDistinctIso.lean` | 82 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVTruncatedKernelDegree.lean` | 139 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVTruncatedModuleBound.lean` | 59 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumGeneratorCoordinates.lean` | 94 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumHomAction.lean` | 221 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumMoments.lean` | 144 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumSignedMoments.lean` | 184 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumSourceComparison.lean` | 207 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumSourceCrossing.lean` | 92 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumSourceWord.lean` | 231 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumWordEvaluation.lean` | 87 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumWordPairing.lean` | 505 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVWeightAbsentFibreInverse.lean` | 49 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVWeightedCapWindows.lean` | 185 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVWeightedDoubleCrossing.lean` | 179 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVWeightedMatrixFunctor.lean` | 106 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVWeightedMatrixFunctorInverse.lean` | 233 |
| `OddMath/QuiverHecke/CyclotomicAction/ExteriorTranslationRelations.lean` | 115 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalRouquierMulticolour.lean` | 165 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerContentCoefficient.lean` | 132 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerError.lean` | 233 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerSupertensorAction.lean` | 365 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerSupertensorGrading.lean` | 151 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerSupertensorScalars.lean` | 161 |
| `OddMath/QuiverHecke/CyclotomicAction/LinearDotCancellation.lean` | 107 |
| `OddMath/QuiverHecke/CyclotomicAction/LocalRelationExamples.lean` | 81 |
| `OddMath/QuiverHecke/CyclotomicAction/MixedMateKernel.lean` | 346 |
| `OddMath/QuiverHecke/CyclotomicAction/Normality.lean` | 84 |
| `OddMath/QuiverHecke/CyclotomicAction/ProbeAppendDotInverse.lean` | 210 |
| `OddMath/QuiverHecke/CyclotomicAction/ProbeGlobalDotInverse.lean` | 72 |
| `OddMath/QuiverHecke/CyclotomicAction/ProbeHeightDotInverse.lean` | 169 |
| `OddMath/QuiverHecke/CyclotomicAction/ProbeSuperDotInverse.lean` | 256 |
| `OddMath/QuiverHecke/CyclotomicAction/ProbeWeightDotInverse.lean` | 226 |
| `OddMath/QuiverHecke/CyclotomicAction/Restriction.lean` | 39 |
| `OddMath/QuiverHecke/CyclotomicAction/ReverseNorm.lean` | 86 |
| `OddMath/QuiverHecke/CyclotomicCoefficients.lean` | 112 |
| `OddMath/QuiverHecke/ELVLastBoundarySeparation.lean` | 173 |
| `OddMath/QuiverHecke/GlobalFactorNondegeneracy.lean` | 116 |
| `OddMath/QuiverHecke/HalfTurn/BoundedDetection.lean` | 59 |
| `OddMath/QuiverHecke/HalfTurn/QuotientEquivalence.lean` | 46 |
| `OddMath/QuiverHecke/SpectatorSeparationExamples.lean` | 54 |
| `OddMath/QuiverHecke/SwappedAssembly/CentralInverse/Extraction.lean` | 179 |
| `OddMath/QuiverHecke/SwappedAssembly/ReservoirDistinctContextCoordinates.lean` | 174 |
| `OddMath/QuiverHecke/SwappedAssembly/Supernatural/MatrixNestedEvaluation.lean` | 60 |
| `OddMath/QuiverHecke/SwappedAssembly/Supernatural/MatrixProductEvaluation.lean` | 46 |
| `OddMath/QuiverHecke/SwappedAssembly/Supernatural/Relations.lean` | 93 |
| `OddMath/QuiverHecke/SwappedAssembly/SupportedTensorEntryParity.lean` | 94 |
| `OddMath/QuiverHecke/SwappedVacuum/LayerAction.lean` | 107 |
| `OddMath/SKM/AdaptedSameColourChoicesExamples.lean` | 36 |
| `OddMath/SKM/BubbleSpecialization.lean` | 134 |
| `OddMath/SKM/BubbleTruncation.lean` | 135 |
| `OddMath/SKM/CupCompletedChoiceExamples.lean` | 34 |
| `OddMath/SKM/FiniteColourRelationsExamples.lean` | 101 |
| `OddMath/SKM/JointScalarDescent.lean` | 59 |
| `OddMath/SKM/LocallyNilpotentMixedInverse.lean` | 232 |
| `OddMath/SKM/OddDotTranslation.lean` | 158 |
| `OddMath/SKM/PairedCoefficientComparison.lean` | 61 |
| `OddMath/SKM/RightClosureCoefficients.lean` | 123 |
| `OddMath/SKM/RouquierDotConjugation.lean` | 71 |
| `OddMath/SKM/RouquierFeedbackIdeal.lean` | 109 |
| `OddMath/SKM/RouquierHomPostSuperInverse.lean` | 253 |
| `OddMath/SKM/RouquierProductInverse.lean` | 159 |
| `OddMath/SKM/ScalarChangeExamples.lean` | 91 |
| `OddMath/SKM/SourceCapAttachmentExamples.lean` | 31 |
| `OddMath/SKM/SourceCapStateExamples.lean` | 28 |
| `OddMath/SKM/SourceCrossAttachmentExamples.lean` | 25 |
| `OddMath/SKM/SourceIdRelabelExamples.lean` | 46 |
| `OddMath/SKM/UpwardNondegeneracyReductionExamples.lean` | 21 |

</details>

## Unreached modules

After the steps above, 38 research modules were reached neither from `master`'s
modules nor from any file under `scripts/`. Eighteen are kept: the inputs of the
Phase 2 work (coefficient and truncated-Rees gradings, graded and lower-degree
parameters), the published-result modules `HomBases`, `Decategorification` and
`GrothendieckIsomorphism` with their imports, and the all-even comparison
`VacuumRouteEvenComparison`; these should become reachable through non-vacuity
examples. The other 20 (2,862 lines) belonged to abandoned routes (fused reservoir
sectors, coupled Rouquier sectors, the conditional swapped theorem) or were
example files of removed lemmas, and were removed.

<details><summary>Removed unreached modules (lines)</summary>

| module | lines |
|---|---|
| `OddMath/Diagrams/OddNilHecke/CyclotomicCutoffKernel.lean` | 20 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAppendPolynomialRows.lean` | 398 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVSourcePolynomialRows.lean` | 535 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVTensorVacuumGenerators.lean` | 165 |
| `OddMath/QuiverHecke/ReservoirCoverage.lean` | 106 |
| `OddMath/QuiverHecke/ReservoirFusedVacuum.lean` | 159 |
| `OddMath/QuiverHecke/ReservoirFusedBubbles.lean` | 222 |
| `OddMath/QuiverHecke/ReservoirFusedDetection.lean` | 76 |
| `OddMath/QuiverHecke/ReservoirFusedSectors.lean` | 181 |
| `OddMath/QuiverHecke/ReservoirVacuumExamples.lean` | 83 |
| `OddMath/QuiverHecke/SpectatorDetectionExamples.lean` | 55 |
| `OddMath/QuiverHecke/SwappedAssembly/Action.lean` | 102 |
| `OddMath/QuiverHecke/SwappedAssembly/Supernatural/MatrixEvaluation.lean` | 51 |
| `OddMath/QuiverHecke/SwappedConditionalNondegeneracy.lean` | 153 |
| `OddMath/SKM/RouquierCoupledMate.lean` | 156 |
| `OddMath/SKM/RouquierCoupledSectors.lean` | 158 |
| `OddMath/SKM/RouquierSchur.lean` | 76 |
| `OddMath/SKM/SameColourCupRowsExamples.lean` | 43 |
| `OddMath/SKM/SameColourSourceFrameExamples.lean` | 53 |
| `OddMath/SKM/SameColourTargetFrameExamples.lean` | 70 |

</details>

## Unused declarations, second pass

The declaration graph of the reduced tree was recomputed and unused declarations were
removed again, with two changes to the criterion of "Method". Topic notes are no longer
roots: a name occurring only in a topic note is removed, and the note then describes an
earlier step of the development. The notes that state current results (README, ERRATA,
STATUS, HANDOFF, NondegeneracyProof, GeneralRoute, FieldScopeBoundary) remain roots. Every
identifier occurring in the remaining Lean code (outside comments, after the removal) is
a root, iterated to a fixed point, so that `simp` lemmas proved by `rfl`, local notations
and `attribute` lines never refer to a removed declaration. Auxiliary declarations
(`_proof_n`, equation lemmas) count with the declaration they belong to.

This removed 909 declarations (716 theorems, 193 definitions; 657 of them in
`QuiverHecke.CyclotomicAction`) from 217 modules. Nine modules were left without
declarations and were removed: `QuiverHecke.CyclotomicAction.ELVAppendSignedMovingSupport`,
`ELVCoefficientPowerPolynomialCap`, `GlobalBraidAlgebra`, `IntertwinerSquareDot` and
`LeadingMoveCoefficients`, `QuiverHecke.ReservoirCoordinates`,
`QuiverHecke.SpectatorSeparation`, `SKM.RouquierAdjacentLeftAdjunction` and
`SKM.RouquierPiSCat`.

## Documentation

The topic notes in `docs/Nondegeneracy/` went from 847 files to 84 (23,227 lines): notes of
removed routes, per-topic checkpoints and superseded inventories were deleted (git history
keeps them). STATUS and HANDOFF were rewritten in place; notes that describe intermediate
steps as open carry a header pointing to STATUS, and the notes on the final route state
which declarations prove them.

## Not done

* Names: the prefix "actual" was dropped from 67 declaration names, and "native" or
  "actual" was dropped from 66 more (a trailing `_native` became `_eq`, for statements
  that evaluate a construction). 15 names keep the word because dropping it would clash
  with an existing name (for example `capRowNative`, `nativeStep`). Many module names in
  `QuiverHecke/CyclotomicAction/` carry the construction label `ELV`/`ELVOld`; renaming
  them touches several hundred files and conflicts with open pull requests.
* Inlining single-use wrappers and merging duplicate statements inside the retained
  route: not attempted beyond the removal of unused declarations.

## Merging into `master` (on hold)

The merge into `master` is on hold until the cleanup and simplification are finished, and
possibly until further extensions (for example the integral form) are in place. The notes
below record the state and the procedure for when it is taken up.

State: `master` has 7 commits not on this branch (merge base `b8822997`): the revert of the
exploratory nondegeneracy additions (`8a8b9820`, removing `Diagrams/OddNilHecke/ExteriorDeformation`,
`SKM/BubbleSpecialization`, `SKM/BubbleTruncation` and their checks), the AGENTS rule keeping
research off `master`, and the cached `NonVacuity` library (already on this branch in another form).

Hazard: a plain merge of this branch into `master` keeps master's deletion of every file this branch
has not changed since the merge base. `BubbleSpecialization` and `BubbleTruncation` are removed
here anyway; `ExteriorDeformation` is unchanged here, so the merge would delete it. The merge must
be checked file by file for these six paths.

Proposed procedure:
1. Finish the cleanup here, with green CI.
2. On a topic branch from this branch, merge `master` with the conflicts resolved toward this
   branch: keep this branch's `OddMath.lean`, `lakefile.lean`, `.github/workflows/build.yml`,
   README; take master's AGENTS text only where it does not conflict, and replace the
   "research stays off master" rule by a statement of what is now on master. Keep or remove
   `ExteriorDeformation` deliberately.
3. Green CI on that branch (full build, axiom audit, NonVacuity).
4. Open a PR into `master` from that branch. Because it already contains `master`, the merge into
   `master` is conflict-free and the result equals the tested tree. Merge commit, then check the
   `master` CI run.
5. Afterwards: README status rows become the headline rows; STATUS/HANDOFF keep only the Phase 2
   work; decide whether `research/odd-nondegeneracy` continues for Phase 2 or Phase 2 moves to
   topic branches against `master` (Alex's decision; AGENTS currently routes uncertain research
   to the research branch).

Size after the cleanup so far: 2904 `OddMath` modules (596,582 lines) against 1321 on
`master`; 104 non-vacuity files against 90. About 1580 research modules would enter `master`.
