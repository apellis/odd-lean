import OddMath.SKM.RightCapAttachment

/-! A literal inverse mate can be reduced without being strictly reduced. -/
namespace NonVacuity.RightCapAttachment
open StringDiagrams StringDiagrams.Chord OddMath.SKM
open OddMath.SKM.RightCapAttachment

private def x : Letter Unit := (false, ())
private def R : List (TMove (Letter Unit)) := [.mv (.cup 0 x)]

private theorem matching : IsMatching₂ [] ([x] ++ [flipL x]) R := by
  constructor
  · exact ⟨by change 0 ≤ 0; omega, trivial⟩
  · rfl

private theorem reduced : Reduced₂ [] R := by
  change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag
  simp

/-- The attached cup-cap zigzag is an actual matching on one downward strand. -/
theorem zigzag_matching : IsMatching₂ [x] [x] (attach [x] R) :=
  attach_matching matching

theorem zigzag_reduced : Reduced₂ [x] (attach [x] R) := attach_reduced matching reduced

/-- This is the concrete obstruction to requiring strict representatives of inverse mates. -/
theorem zigzag_not_strict : ¬ StrictReduced₂ [x] (attach [x] R) := by
  intro h
  have hc := h.2
  change ([2, 2] : List ℕ).Nodup at hc
  simp at hc

private def ds : List (DTMove Unit) := [.tm (.mv (.cup 0 x)), .dt 0]

/-- The decorated inverse mate uses literal right-whiskering and a final cap. -/
theorem dotted_layers :
    dLay [x] (attachMoves [x] ds) =
      (dLay [] ds).map (xwhL [] [x]) ++ (xCapL x).map (xwhL [x] []) := by
  apply dLay_attachMoves matching (show DTMove.tmoves ds = R from rfl)
  change 0 < 2 ∧ True
  simp

theorem dotted_position : DTMove.dotPts (attachMoves [x] ds) = [(1, 0)] := by
  rw [dotPts_attachMoves]
  rfl

#print axioms zigzag_matching
#print axioms zigzag_reduced
#print axioms zigzag_not_strict
#print axioms dotted_layers
#print axioms dotted_position
end NonVacuity.RightCapAttachment
