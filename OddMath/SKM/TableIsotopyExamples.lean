import OddMath.SKM.TableIsotopy

namespace OddMath.SKM.TableIsotopyExamples
open StringDiagrams StringDiagrams.Chord
variable {I X : Type*} [AddCommGroup X] (D : Datum I X) (sy : Symmetrizer D) (μ : X)

/-- Nonempty local pitchfork, including mixed orientations and repeated colours. -/
theorem pitchfork (a b : Letter I) :
    tableDegree D sy μ (chordLay [b] [.cup 0 a, .cross 1]) =
      tableDegree D sy μ (chordLay [b] [.cup 1 a, .cross 0]) ∧
    xpar D μ (chordLay [b] [.cup 0 a, .cross 1]) =
      xpar D μ (chordLay [b] [.cup 1 a, .cross 0]) :=
  tableDegree_xpar_step D sy μ (Step.pitch 0 a) [b] (by
    simp [Fits, Move.Ok, Move.len])

/-- A cup below the pitchfork supplies a genuine one-sided contextual consumer. -/
theorem contextual_pitchfork (i j : I) :
    tableDegree D sy μ (chordLay [] [.cup 0 (false, j), .cup 0 (true, i), .cross 1]) =
      tableDegree D sy μ (chordLay [] [.cup 0 (false, j), .cup 1 (true, i), .cross 0]) ∧
    xpar D μ (chordLay [] [.cup 0 (false, j), .cup 0 (true, i), .cross 1]) =
      xpar D μ (chordLay [] [.cup 0 (false, j), .cup 1 (true, i), .cross 0]) := by
  apply tableDegree_xpar_equiv D sy μ
    (Chord.Equiv.of_step (Step.pitch 0 (true, i)) |>.append_left [.cup 0 (false, j)]) []
  simp [Fits, Move.Ok, Move.len]

/-- The table is anchored to the degree of an ordinary nonempty crossing diagram. -/
theorem ordinary_crossing (i j : I) :
    tableDegree D sy μ ((crossL [] i j []).map ofL) =
      Diagram.degree (gdeg D sy) (mkD D μ (crossL [] i j []) (show SChain [up i, up j] (crossL [] i j []) [up j, up i] from ⟨rfl, rfl⟩)) ∧
    tableDegree D sy μ ((crossL [] i j []).map ofL) = sy.d i * D.d i j := by
  exact ⟨tableDegree_diagram D sy μ _ _, by rw [tableDegree_ofL, gsum_crossL]⟩

end OddMath.SKM.TableIsotopyExamples
