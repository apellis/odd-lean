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

## Remaining critical chain

1. Combine the proved prescribed source/crossing decompositions and polynomial
   boundary in the exact categorical diagram; derive the snake/
   augmented inverse at every height, including zero. Supply the required
   coefficient compatibility, naturality and integer-degree comparisons.
2. Construct the full-ELV factor families from that inverse and the independent
   content induction maps; finish their composed mixed braid and multicolour
   presentation comparison with algebra parameters `parameterTwist Sc`.
3. Supply concrete probe/reservoir data, crossing coefficients and whole swapped
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

The reviewed source snapshot is
[e522e775](https://github.com/apellis/odd-lean/commit/e522e7753f37c5510c628ea83a90902a3abd7dea).
Its [branch build](https://github.com/apellis/odd-lean/actions/runs/41081958632)
was cancelled; no full-green claim is made for that exact snapshot.
Its parent [b23baa2 build](https://github.com/apellis/odd-lean/actions/runs/41076454671)
passed. Subsequent commits must use their own CI evidence.
Required gates remain full build with warnings as errors, axiom audit and
non-vacuity consumers. Finite Python models are evidence about their instances,
not proofs of the general action or conjecture.
