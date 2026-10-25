import OddMath.QuiverHecke.WeightedDeformationIdeal
import OddMath.SKM.MixedCrossingLocalExamples

noncomputable section
open CategoryTheory OddMath.QuiverHecke OddMath.SKM
open scoped Classical

private def i : {i : Bool // MixedCrossingLocalExamples.oddDatum.parity i = 1} := ⟨false, rfl⟩

/-- At even cutoff six, the source coefficient relation has weight seven. -/
example : SYM.delta MixedCrossingLocalExamples.oddDatum ℚ i *
    SYM.e MixedCrossingLocalExamples.oddDatum ℚ false 2 ∈
    SYM.CoefficientAtLeast MixedCrossingLocalExamples.oddDatum ℚ 7 :=
  SYM.elvTopRelation_mem_coefficientAtLeast _ _ i 2

/-- The exterior-flat alternative kills a weight-six elementary coefficient,
so it is equally admissible for the cutoff-six support estimate. -/
example : SYM.e MixedCrossingLocalExamples.oddDatum ℚ false 2 ∈
    SYM.CoefficientAtLeast MixedCrossingLocalExamples.oddDatum ℚ 6 := by
  simpa [SYM.elementaryWeight, MixedCrossingLocalExamples.oddDatum] using
    SYM.elementary_mem_coefficientAtLeast MixedCrossingLocalExamples.oddDatum ℚ false 2

#print axioms weightedRelationSpan_comp
#print axioms comp_weightedRelationSpan
#print axioms highCoefficient_identity_mem_relationSpan
#print axioms elvTopRelation_mem_relationSpan
#print axioms oddTopElementary_mem_relationSpan
#print axioms SYM.coefficientBasis_delta
