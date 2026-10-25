import OddMath.SKM.WeakMateLayers

/-! Literal nested cup/cap layers on a nonempty two-strand upward matching. -/
namespace NonVacuity.WeakMateLayers
open StringDiagrams StringDiagrams.Chord OddMath.SKM
private def u : Letter Unit := (true, ())
private theorem hm : IsMatching₂ (ups [()] ++ [u]) ([u] ++ ups [()]) [] := ⟨trivial, rfl⟩

theorem literal_mate_layers :
    dLay ([u] ++ dns [()]) (WeakMate.moves [()] [u] (ups [()]) []) =
      (partialRightMateL [()] [()] [u] [u] []).map ofL := by
  classical
  obtain ⟨q, hq⟩ := matching_bounded_points hm
  have hd : Decorates₂ (ups [()] ++ [u]) [] q (strandCounts (fun _ : MatchingStrand (ups [()] ++ [u]) [] => 0)) [] := by
    constructor
    · rfl
    · simp [DTMove.dotPts, strandCounts]
  exact WeakMate.dLay_moves hm q hq (fun _ => 0) hd rfl

#print axioms literal_mate_layers
#print axioms WeakMate.dLay_moves
end NonVacuity.WeakMateLayers
