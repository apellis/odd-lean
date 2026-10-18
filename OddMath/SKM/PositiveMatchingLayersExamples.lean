import OddMath.SKM.PositiveMatchingLayers

/-! Concrete boundary cases for the crossing-layer extraction. -/

namespace OddMath.SKM.PositiveMatchingLayersExamples
open StringDiagrams.Chord

private def emptyColour : Fin 0 → Empty := Fin.elim0

private theorem empty_matching : IsMatching₂
    (List.ofFn fun r => (true, emptyColour r))
    (List.ofFn fun r => (true, emptyColour r)) [] := ⟨trivial, rfl⟩

private theorem empty_reduced : StrictReduced₂
    (List.ofFn fun r => (true, emptyColour r)) [] := by
  exact ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩

example : ∀ m ∈ ([] : List (TMove (Letter Empty))), ∃ p, m = .mv (.cross p) :=
  empty_matching.positive_crossing_moves emptyColour emptyColour empty_reduced

example : ∃ L : List (LayerData Empty), SChain [] L [] ∧
    L.map ofL = tLay [] [] ∧ ∀ x ∈ L, ∃ i j, x.2.1 = Shape.cross i j := by
  simpa using positive_tLay_ofL emptyColour emptyColour empty_matching empty_reduced

private def repeatedColour : Fin 2 → Unit := fun _ => ()
private def swapMoves : List (TMove (Letter Unit)) := [.mv (.cross 0)]

private theorem swap_matching : IsMatching₂
    (List.ofFn fun r => (true, repeatedColour r))
    (List.ofFn fun r => (true, repeatedColour r)) swapMoves := by
  constructor
  · change 3 < 4 ∧ True
    decide
  · rfl

private theorem swap_reduced : StrictReduced₂
    (List.ofFn fun r => (true, repeatedColour r)) swapMoves := by
  constructor
  · constructor
    · exact List.nodup_singleton _
    · intro z hz
      change z ∈ [_] at hz
      obtain rfl := List.mem_singleton.mp hz
      decide
  · exact List.nodup_nil

-- Equal colours do not identify the strands: the endpoint permutation exchanges them.
example : ∀ r : Fin 2, Same
    (pairing₂ (List.ofFn fun r => (true, repeatedColour r)) swapMoves)
    (2 - 1 - r.val) (2 + ((Equiv.swap 0 1) r).val) := by
  intro r
  fin_cases r <;> constructor <;> decide

example : ∀ m ∈ swapMoves, ∃ p, m = TMove.mv (Move.cross p) :=
  swap_matching.positive_crossing_moves repeatedColour repeatedColour swap_reduced

example : ∃ L : List (LayerData Unit),
    SChain (List.ofFn fun r => (true, repeatedColour r)) L
      (List.ofFn fun r => (true, repeatedColour r)) ∧
    L.map ofL = tLay (List.ofFn fun r => (true, repeatedColour r)) swapMoves ∧
    ∀ x ∈ L, ∃ i j, x.2.1 = Shape.cross i j :=
  positive_tLay_ofL repeatedColour repeatedColour swap_matching swap_reduced

end OddMath.SKM.PositiveMatchingLayersExamples
