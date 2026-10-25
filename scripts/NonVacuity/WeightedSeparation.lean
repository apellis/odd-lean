import OddMath.QuiverHecke.WeightedSeparation

/-! Concrete score checks include the out-of-range-generator convention. -/

open OddMath.QuiverHecke

example : positionedScore 2 [.dot 0, .cross 0, .dot 1] = 1 := by decide
example : positionedScore 1 [.dot 7, .cross 0] = 0 := by decide
example : positionedScore 3 (cw [0, 1, 0]) = -3 := by decide

#print axioms filt_zero_le_boundedScore_zero
#print axioms bounded_correction_ctx
#print axioms weighted_approx_step
#print axioms weighted_braid_move

noncomputable section
open CategoryTheory StringDiagrams
variable {I X k : Type} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k)

/-- A two-strand dot-crossing-dot word has score one in its canonical expansion. -/
example (i j : I) :
    cl D Sc [i, j] (tgt [i, j] [.dot 0, .cross 0, .dot 1])
      [.dot 0, .cross 0, .dot 1] (sChain_pl _ _) ∈
    WeightedNF D Sc [i, j] (tgt [i, j] [.dot 0, .cross 0, .dot 1]) 1 1 := by
  have hs : positionedScore 2 [.dot 0, .cross 0, .dot 1] = 1 := by decide
  simpa only [crossCount, PG.isCross, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, zero_add, add_zero, List.length_cons, List.length_nil, hs]
    using word_mem_weightedNF D Sc [.dot 0, .cross 0, .dot 1] (sChain_pl [i, j] _)

#print axioms boundedScore_le_weightedNF
#print axioms word_mem_weightedNF
