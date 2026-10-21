import OddMath

/-! BE2 Lemma 11.6: two odd colours and the negative-weight coefficient diagnostic. -/
noncomputable section
open OddMath OddMath.SKM OddMath.SKM.K0Relations
open OddMath.CoveringQuantum
open OddMath.CoveringQuantum.UDot.ContextualExchangeExamples

example : WeightRelations DimensionFormulaExamples.scalars
    twoOddDatum.skmSymmetrizer DimensionFormulaExamples.homogeneous :=
  K0RelationsExamples.odd_weights

-- These applications check all weights and both distinct odd colours.
#check K0RelationsExamples.odd_distinct (fun _ => -2)
#check K0RelationsExamples.odd_comm false (fun _ => 2)
#check K0RelationsExamples.odd_comm true (fun _ => -2)
#check K0RelationsExamples.zero_weight
#check K0RelationsExamples.even_integral
#check K0RelationsExamples.positive_two
#check K0RelationsExamples.negative_two
#check weight_mixed_relations DimensionFormulaExamples.scalars
  twoOddDatum.skmSymmetrizer DimensionFormulaExamples.homogeneous
#check covering_comm_same twoOddDatum DimensionFormulaExamples.scalars
  DimensionFormulaExamples.homogeneous false (fun _ => -2)

example : qpInt (Units.mk0 (2 : ℚ) (by norm_num)) (-1) (-2) ≠
    -((-1 : ℚ) * qpNat (Units.mk0 (2 : ℚ) (by norm_num)) (-1) 2) :=
  K0RelationsExamples.printed_negative_coefficient_fails
