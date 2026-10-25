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
