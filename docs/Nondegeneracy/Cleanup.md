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

## Sizes

| | `OddMath` modules | lines | non-vacuity files | lines |
|---|---|---|---|---|
| research tip before cleanup | 3102 | 643,236 | 1382 | 116,274 |
| after removing unused modules | 2800 | 596,776 | 101 | 4,415 |
| `master` | 1321 | | 90 | |

The Phase 1 theorem alone uses declarations from 1584 modules; the remaining research
modules after this step are live because a retained result uses at least one of their
declarations.

## Removed modules

302 `OddMath` modules (47,000 lines) contribute no declaration to
any retained result: earlier routes (cyclotomic-action content and append constructions,
earlier Rouquier mate and inverse constructions, earlier swapped-assembly variants) and
their example files. 1280 research non-vacuity files (about 111,900 lines)
exercised intermediate lemmas only and are removed with them. Git history keeps all of them.

<details><summary>Removed `OddMath` modules (lines)</summary>

| module | lines |
|---|---|
| `OddMath/Algebra/FrobeniusResolvent.lean` | 78 |
| `OddMath/Diagrams/OddNilHecke/CyclotomicExteriorObstruction.lean` | 67 |
| `OddMath/Diagrams/OddNilHecke/CyclotomicNorm.lean` | 71 |
| `OddMath/Diagrams/OddNilHecke/SeparatedCrossing.lean` | 62 |
| `OddMath/Diagrams/OddNilHecke/SeparatedSquareNorm.lean` | 30 |
| `OddMath/QuiverHecke/CyclotomicAction/ActionSupercategory.lean` | 106 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendContentBoundary.lean` | 165 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendContentCorner.lean` | 174 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendContentCrossingImage.lean` | 210 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendContentMackeyMap.lean` | 168 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendContentRhoCoordinates.lean` | 251 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendContentShortFactor.lean` | 138 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendContentShortImage.lean` | 215 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendCornerTensor.lean` | 338 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendEquivalence.lean` | 333 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendLeftCrossing.lean` | 762 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendTensorCoordinates.lean` | 110 |
| `OddMath/QuiverHecke/CyclotomicAction/AppendTensorRightDot.lean` | 202 |
| `OddMath/QuiverHecke/CyclotomicAction/BoundaryWindow.lean` | 327 |
| `OddMath/QuiverHecke/CyclotomicAction/Comparison.lean` | 54 |
| `OddMath/QuiverHecke/CyclotomicAction/ContentSupport.lean` | 72 |
| `OddMath/QuiverHecke/CyclotomicAction/CornerPairing.lean` | 189 |
| `OddMath/QuiverHecke/CyclotomicAction/CrossingTransformation.lean` | 102 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAffineDetection.lean` | 123 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAppendKernel.lean` | 132 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAppendPolynomialIdempotents.lean` | 105 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAppendPolynomialRows.lean` | 398 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAppendProjective.lean` | 129 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAppendRows.lean` | 131 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAppendRowsEquivalence.lean` | 378 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAppendSignedMovingSupport.lean` | 166 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVAppendSupport.lean` | 61 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVBoundaryRowDivision.lean` | 262 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVBoundaryRowSplitting.lean` | 299 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVBoundarySnake.lean` | 171 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVBoundedSourceDetection.lean` | 107 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVCapCoordinateTransport.lean` | 182 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVCoefficientAppendMaps.lean` | 105 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVCoefficientPowerNilpotence.lean` | 146 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVCoefficientPowerNonpositiveCap.lean` | 53 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVCoefficientPowerParity.lean` | 77 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVCoefficientPowerPolynomialCap.lean` | 118 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVCoefficientWindowTensor.lean` | 101 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentAbsentUnitFamily.lean` | 53 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentAssociativityTensor.lean` | 52 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentBlockMatrixCaps.lean` | 39 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentBlockMatrixCharts.lean` | 128 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentBraidTransforms.lean` | 173 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentCastCoherence.lean` | 66 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentCrossingTransforms.lean` | 88 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentDistinctIso.lean` | 82 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentDotTransforms.lean` | 144 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentExactness.lean` | 152 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentGridMatrixFunctorInverse.lean` | 121 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentMatrixComponents.lean` | 181 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentMissingLocal.lean` | 39 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentMissingUnitNaturality.lean` | 50 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVContentMissingUnitRows.lean` | 51 |
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
| `OddMath/QuiverHecke/CyclotomicAction/ELVEndpointPresheaf.lean` | 174 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVGradedKernelEquivalence.lean` | 57 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVIndResKernelNaturality.lean` | 112 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVInductionAssociativity.lean` | 108 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVInductionGridComposition.lean` | 126 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVInductionGridMatrixFunctor.lean` | 239 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVInductionKernelGrading.lean` | 85 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVInductionRepresentable.lean` | 264 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVInductionSquareComposition.lean` | 110 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVInductionSquareTransform.lean` | 128 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVInductionUnitNaturality.lean` | 41 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVJointPBWDetection.lean` | 117 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVLowerDegree.lean` | 84 |
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
| `OddMath/QuiverHecke/CyclotomicAction/ELVParityRestrictionComparison.lean` | 113 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVPolynomialIdempotents.lean` | 117 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVPositiveCrossing.lean` | 118 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVPowerWordDistinctCrossing.lean` | 325 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVPowerWordHomCoordinates.lean` | 242 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVPowerWordPairCrossing.lean` | 394 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVPowerWordWhiskering.lean` | 201 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeAppendCrossing.lean` | 131 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeCapRowComparison.lean` | 158 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeCoefficientCapUniqueness.lean` | 92 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeCoefficientExpansion.lean` | 155 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeCounitComparison.lean` | 216 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeDottedComparison.lean` | 120 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeDoubleAppend.lean` | 232 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeDoubleCrossing.lean` | 60 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeEvaluatedBraid.lean` | 80 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeEvaluatedDistinctMate.lean` | 135 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeExtensionParity.lean` | 100 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeExtensionPolynomial.lean` | 86 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeExtensionRows.lean` | 94 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeFiniteMatrixComparison.lean` | 104 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeLocalPreAdjunction.lean` | 141 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeMateComparison.lean` | 222 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeMatrixEntryComparison.lean` | 344 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeMatrixFamilyCharts.lean` | 229 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeMatrixInverse.lean` | 195 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeMatrixInverseCandidates.lean` | 115 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeOldDotUnit.lean` | 104 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeReindexPair.lean` | 235 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeRouquierCap.lean` | 225 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeSeparatedBends.lean` | 180 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeVacuumLocalCap.lean` | 148 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVProbeWeightTripleCoordinates.lean` | 69 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVQPDivisionEquiv.lean` | 294 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVQPNumerator.lean` | 295 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVQuotientPresheaf.lean` | 160 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVRawAppendSpanning.lean` | 134 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVRawCoefficientComparison.lean` | 138 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVRawMixedCoefficient.lean` | 205 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVRawMixedEvenMate.lean` | 129 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVRawMixedMate.lean` | 88 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVRestrictionMatrixCharts.lean` | 77 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVSCatRectangularMate.lean` | 33 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVSourcePolynomialQuotient.lean` | 85 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVSourcePolynomialRows.lean` | 535 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVSourceProjective.lean` | 158 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVSourceRows.lean` | 251 |
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
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumRepresentable.lean` | 172 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumSignedMoments.lean` | 184 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumSourceComparison.lean` | 207 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumSourceCrossing.lean` | 92 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumSourceWord.lean` | 231 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumWordEvaluation.lean` | 87 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVVacuumWordPairing.lean` | 505 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVWeightAbsentFibreInverse.lean` | 49 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVWeightAbsentUnitFamily.lean` | 89 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVWeightedCapWindows.lean` | 185 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVWeightedDoubleAppend.lean` | 91 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVWeightedDoubleCrossing.lean` | 179 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVWeightedMatrixFunctor.lean` | 106 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVWeightedMatrixFunctorInverse.lean` | 233 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVWeightedPairAppend.lean` | 186 |
| `OddMath/QuiverHecke/CyclotomicAction/ELVWeightedPolynomialCaps.lean` | 341 |
| `OddMath/QuiverHecke/CyclotomicAction/ExteriorTranslationRelations.lean` | 115 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalBraidAlgebra.lean` | 199 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalCross.lean` | 148 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalHeightAdjunction.lean` | 630 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalHeightBlockCross.lean` | 132 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalHeightBraid.lean` | 275 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalHeightCrossing.lean` | 675 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalHeightDot.lean` | 233 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalHeightMixedInductionSquare.lean` | 160 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalHeightMixedSlides.lean` | 440 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalHeightSlides.lean` | 497 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalInduction.lean` | 260 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalMixedSlideAlgebra.lean` | 291 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalRestriction.lean` | 116 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalRouquierData.lean` | 114 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalRouquierFamily.lean` | 94 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalRouquierMulticolour.lean` | 165 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalSlideAlgebra.lean` | 383 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalWeightBraid.lean` | 264 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalWeightMixedSlides.lean` | 370 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalWeightRestriction.lean` | 219 |
| `OddMath/QuiverHecke/CyclotomicAction/GlobalWeightSlides.lean` | 378 |
| `OddMath/QuiverHecke/CyclotomicAction/InductionComposition.lean` | 321 |
| `OddMath/QuiverHecke/CyclotomicAction/InductionFunctorComparison.lean` | 133 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerContent.lean` | 371 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerContentCoefficient.lean` | 132 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerContentDot.lean` | 243 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerContentTensor.lean` | 294 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerDotGrading.lean` | 135 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerError.lean` | 233 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerRightCoefficient.lean` | 356 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerRightDot.lean` | 121 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerRightPolynomial.lean` | 196 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerSkewAction.lean` | 328 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerSquareDot.lean` | 78 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerSupertensorAction.lean` | 365 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerSupertensorGrading.lean` | 151 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerSupertensorScalars.lean` | 161 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerTargetTensor.lean` | 208 |
| `OddMath/QuiverHecke/CyclotomicAction/IntertwinerTensor.lean` | 66 |
| `OddMath/QuiverHecke/CyclotomicAction/LastCrossing.lean` | 227 |
| `OddMath/QuiverHecke/CyclotomicAction/LastDot.lean` | 145 |
| `OddMath/QuiverHecke/CyclotomicAction/LeadingMoveCoefficients.lean` | 109 |
| `OddMath/QuiverHecke/CyclotomicAction/LinearDotCancellation.lean` | 107 |
| `OddMath/QuiverHecke/CyclotomicAction/LocalRelationExamples.lean` | 81 |
| `OddMath/QuiverHecke/CyclotomicAction/MixedComparison.lean` | 108 |
| `OddMath/QuiverHecke/CyclotomicAction/MixedMateKernel.lean` | 346 |
| `OddMath/QuiverHecke/CyclotomicAction/Normality.lean` | 84 |
| `OddMath/QuiverHecke/CyclotomicAction/PrependCoefficientCoordinates.lean` | 86 |
| `OddMath/QuiverHecke/CyclotomicAction/PrependDotCancellation.lean` | 134 |
| `OddMath/QuiverHecke/CyclotomicAction/PrependEquivalence.lean` | 332 |
| `OddMath/QuiverHecke/CyclotomicAction/PrependTensorCoordinates.lean` | 110 |
| `OddMath/QuiverHecke/CyclotomicAction/PrependTwistCoordinates.lean` | 180 |
| `OddMath/QuiverHecke/CyclotomicAction/ProbeAppendDotInverse.lean` | 210 |
| `OddMath/QuiverHecke/CyclotomicAction/ProbeGlobalDotInverse.lean` | 72 |
| `OddMath/QuiverHecke/CyclotomicAction/ProbeHeightDotInverse.lean` | 169 |
| `OddMath/QuiverHecke/CyclotomicAction/ProbeSuperDotInverse.lean` | 256 |
| `OddMath/QuiverHecke/CyclotomicAction/ProbeWeightDotInverse.lean` | 226 |
| `OddMath/QuiverHecke/CyclotomicAction/Restriction.lean` | 39 |
| `OddMath/QuiverHecke/CyclotomicAction/ReverseNorm.lean` | 86 |
| `OddMath/QuiverHecke/CyclotomicAction/RouquierCupCapKernel.lean` | 263 |
| `OddMath/QuiverHecke/CyclotomicAction/RouquierKernelComparison.lean` | 285 |
| `OddMath/QuiverHecke/CyclotomicAction/RouquierMateKernel.lean` | 241 |
| `OddMath/QuiverHecke/CyclotomicAction/Square.lean` | 98 |
| `OddMath/QuiverHecke/CyclotomicAction/SuperAdjunction.lean` | 103 |
| `OddMath/QuiverHecke/CyclotomicAction/SuperAdjunctionCounit.lean` | 223 |
| `OddMath/QuiverHecke/CyclotomicAction/SuperAdjunctionUnit.lean` | 120 |
| `OddMath/QuiverHecke/CyclotomicAction/SuperCrossing.lean` | 115 |
| `OddMath/QuiverHecke/CyclotomicAction/SuperDot.lean` | 140 |
| `OddMath/QuiverHecke/CyclotomicAction/SuperInduction.lean` | 146 |
| `OddMath/QuiverHecke/CyclotomicAction/SuperRestriction.lean` | 149 |
| `OddMath/QuiverHecke/CyclotomicCoefficients.lean` | 112 |
| `OddMath/QuiverHecke/ELVLastBoundarySeparation.lean` | 173 |
| `OddMath/QuiverHecke/GlobalFactorNondegeneracy.lean` | 116 |
| `OddMath/QuiverHecke/HalfTurn/BoundedDetection.lean` | 59 |
| `OddMath/QuiverHecke/HalfTurn/QuotientEquivalence.lean` | 46 |
| `OddMath/QuiverHecke/PairingExtensionAction.lean` | 42 |
| `OddMath/QuiverHecke/PairingExtensionObservation.lean` | 79 |
| `OddMath/QuiverHecke/ReservoirCoordinates.lean` | 68 |
| `OddMath/QuiverHecke/ReservoirCoverage.lean` | 106 |
| `OddMath/QuiverHecke/SpectatorSeparation.lean` | 81 |
| `OddMath/QuiverHecke/SpectatorSeparationExamples.lean` | 54 |
| `OddMath/QuiverHecke/SwappedAssembly/CentralInverse/Extraction.lean` | 179 |
| `OddMath/QuiverHecke/SwappedAssembly/CentralInverse/ModuleCoefficients.lean` | 215 |
| `OddMath/QuiverHecke/SwappedAssembly/CentralInverse/PositiveVacuumWindow.lean` | 75 |
| `OddMath/QuiverHecke/SwappedAssembly/CentralInverse/RegularCoefficientBound.lean` | 141 |
| `OddMath/QuiverHecke/SwappedAssembly/CentralInverse/VacuumWindow.lean` | 94 |
| `OddMath/QuiverHecke/SwappedAssembly/ReservoirDistinctContextCoordinates.lean` | 174 |
| `OddMath/QuiverHecke/SwappedAssembly/Supernatural/MatrixNestedEvaluation.lean` | 60 |
| `OddMath/QuiverHecke/SwappedAssembly/Supernatural/MatrixProductEvaluation.lean` | 46 |
| `OddMath/QuiverHecke/SwappedAssembly/Supernatural/Relations.lean` | 93 |
| `OddMath/QuiverHecke/SwappedAssembly/SupportedTensorEntryParity.lean` | 94 |
| `OddMath/QuiverHecke/SwappedVacuum/LayerAction.lean` | 107 |
| `OddMath/QuiverHecke/SwappedVacuumBasisEvaluation.lean` | 137 |
| `OddMath/SKM/AdaptedSameColourChoicesExamples.lean` | 36 |
| `OddMath/SKM/BubbleSpecialization.lean` | 134 |
| `OddMath/SKM/BubbleTruncation.lean` | 135 |
| `OddMath/SKM/CupCompletedChoiceExamples.lean` | 34 |
| `OddMath/SKM/FiniteColourRelationsExamples.lean` | 101 |
| `OddMath/SKM/JointScalarDescent.lean` | 59 |
| `OddMath/SKM/LocallyNilpotentMixedInverse.lean` | 232 |
| `OddMath/SKM/OddDotTranslation.lean` | 158 |
| `OddMath/SKM/PairedCoefficientComparison.lean` | 61 |
| `OddMath/SKM/ReservoirBubbleCoordinates.lean` | 86 |
| `OddMath/SKM/RightClosureCoefficients.lean` | 123 |
| `OddMath/SKM/RouquierAdjacentLeftAdjunction.lean` | 63 |
| `OddMath/SKM/RouquierCoupledMate.lean` | 156 |
| `OddMath/SKM/RouquierDotConjugation.lean` | 71 |
| `OddMath/SKM/RouquierFeedbackIdeal.lean` | 109 |
| `OddMath/SKM/RouquierHomPostSuperInverse.lean` | 253 |
| `OddMath/SKM/RouquierMateCoordinates.lean` | 75 |
| `OddMath/SKM/RouquierMateProjection.lean` | 54 |
| `OddMath/SKM/RouquierMateSeries.lean` | 117 |
| `OddMath/SKM/RouquierMateSlide.lean` | 57 |
| `OddMath/SKM/RouquierPiSCat.lean` | 102 |
| `OddMath/SKM/RouquierPreAdjunction.lean` | 139 |
| `OddMath/SKM/RouquierProductInverse.lean` | 159 |
| `OddMath/SKM/ScalarChangeExamples.lean` | 91 |
| `OddMath/SKM/SourceCapAttachmentExamples.lean` | 31 |
| `OddMath/SKM/SourceCapStateExamples.lean` | 28 |
| `OddMath/SKM/SourceCrossAttachmentExamples.lean` | 25 |
| `OddMath/SKM/SourceIdRelabelExamples.lean` | 46 |
| `OddMath/SKM/UpwardNondegeneracyReductionExamples.lean` | 21 |

</details>

## Next steps

1. Remove unused declarations inside live research modules (about 5,600 named theorems and
   definitions that no retained result uses), then modules that become empty.
2. Prune topic notes in `docs/Nondegeneracy/` for removed routes; keep STATUS and
   HANDOFF short and accurate; remove the exploratory scripts in `scripts/Nondegeneracy/`.
3. Inside the retained code: inline single-use wrappers, merge duplicate statements,
   rename stage-label names to mathematical names, and correct docstrings that describe
   proved steps as open or conditional.
4. A proposal for merging the branch into `master`.
