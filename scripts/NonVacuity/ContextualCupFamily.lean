import OddMath.SKM.ContextualCupFamily

open OddMath.SKM StringDiagrams StringDiagrams.Chord
noncomputable section
universe u
variable {I : Type u}

/-- A cup added between arbitrary surviving through-strand contexts. -/
example (P Q : List (Letter I)) (ε : Bool) (i : I) :
    IsMatching₂ (P ++ Q) (P ++ (ε, i) :: (!ε, i) :: Q)
      [.mv (.cup P.length (ε, i))] ∧
    StrictReduced₂ (P ++ Q) [.mv (.cup P.length (ε, i))] := by
  have hm : IsMatching₂ (P ++ Q) (P ++ Q) [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ (P ++ Q) [] := by
    simp [StrictReduced₂, Reduced₂, critPts₂, tRun, tCrit, tStart]
  exact strict_matching_append_cup (P ++ Q) P Q ε i hm hr

#print axioms OddMath.SKM.strict_matching_append_cup
#print axioms OddMath.SKM.cup_representatives_equiv
#print axioms OddMath.SKM.cup_decorated_labels_equiv
