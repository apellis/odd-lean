import OddMath.SKM.ContextualCrossFamily

open OddMath.SKM StringDiagrams StringDiagrams.Chord
noncomputable section
universe u
variable {I : Type u}

/-- The new construction covers arbitrary distinct endpoint classes. -/
example (a P Q : List (Letter I)) (x y : Letter I)
    (T : List (TMove (Letter I))) (hT : IsMatching₂ a (P ++ x :: y :: Q) T)
    (hn : ¬ Same (pairing₂ a T) (a.length + P.length) (a.length + P.length + 1)) :
    ∃ R S, IsMatching₂ a (P ++ x :: y :: Q) R ∧ StrictReduced₂ a R ∧
      IsMatching₂ a (P ++ y :: x :: Q) S ∧ StrictReduced₂ a S ∧
      Iso (pairing₂ a R) (pairing₂ a T) ∧
      Iso (pairing₂ a S) (swapAt (pairing₂ a R) (a.length + P.length)) ∧
      (S = R ++ [.mv (.cross P.length)] ∨ R = S ++ [.mv (.cross P.length)]) :=
  exists_adapted_distinct_pair a P Q x y hT hn

/-- An actual crossed pair of through strands, with nonempty boundary. -/
example (x y : Letter I) :
    IsMatching₂ [x, y] [y, x] [.mv (.cross 0)] :=
  matching_append_cross [x, y] [] [] x y (R := []) ⟨trivial, rfl⟩

#print axioms OddMath.SKM.exists_adapted_distinct_pair
#print axioms OddMath.SKM.terminalCrossCountsEquiv_apply
