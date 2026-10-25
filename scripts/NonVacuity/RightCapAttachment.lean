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

private def u : Letter Unit := (true, ())
private def twoUps : List (Letter Unit) := [u, u]
private def threeDots : List (DTMove Unit) := [.dt 0, .dt 1, .dt 0]

private theorem identity_matching : IsMatching₂ twoUps ([] ++ twoUps) [] := ⟨trivial, rfl⟩
private theorem identity_reduced : Reduced₂ twoUps [] := by
  change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag
  simp

/-- Two successive right caps retain the actual matching and weak reducedness. -/
theorem two_caps_reduced :
    IsMatching₂ (twoUps ++ dualW twoUps) [] (suffixMatching [] twoUps []) ∧
      Reduced₂ (twoUps ++ dualW twoUps) (suffixMatching [] twoUps []) :=
  ⟨suffix_matching identity_matching, suffix_reduced identity_matching identity_reduced⟩

/-- Repeated dots and both right caps use the checked literal layer bridge. -/
theorem two_caps_dotted_layers :
    dLay (twoUps ++ dualW twoUps) (suffixMoves [] twoUps threeDots) =
      suffixLayers [] twoUps (dLay twoUps threeDots) := by
  apply dLay_suffixMoves identity_matching (show DTMove.tmoves threeDots = [] from rfl)
  change 0 < 2 ∧ 1 < 2 ∧ 0 < 2 ∧ True
  decide

#print axioms zigzag_matching
#print axioms zigzag_reduced
#print axioms zigzag_not_strict
#print axioms dotted_layers
#print axioms dotted_position
#print axioms two_caps_reduced
#print axioms two_caps_dotted_layers
#print axioms OddMath.SKM.RightCapAttachment.onStrand_attach
#print axioms OddMath.SKM.RightCapAttachment.attach_decorates
#print axioms OddMath.SKM.RightCapAttachment.suffix_decorates
end NonVacuity.RightCapAttachment
