import OddMath.SKM.TwoSidedGrading
import OddMath.SKM.PositivePointGradingExamples

/-! Nonempty cap-to-zigzag normalization through the reduced comparison theorem. -/

namespace OddMath.SKM.TwoSidedGradingExamples
open StringDiagrams StringDiagrams.Chord
variable {I X : Type*} [AddCommGroup X] (D : Datum I X) (sy : Symmetrizer D)

/-- Normalize the raw cup-cap zigzag to the identity on a nonempty downward boundary. -/
theorem cap_zigzag_normalization (i : I) (μ : X) :
    tableDegree D sy μ (tLay [(false, i)] []) =
      tableDegree D sy μ (tLay [(false, i)]
        [.mv (.cup 0 (false, i)), .cap 1]) ∧
    xpar D μ (tLay [(false, i)] []) =
      xpar D μ (tLay [(false, i)]
        [.mv (.cup 0 (false, i)), .cap 1]) := by
  have hm : IsMatching₂ [(true, i), (false, i)] [] [.cap 0] := by
    constructor
    · refine ⟨?_, trivial⟩
      exact ⟨(2, (true, i)), (0, (false, i)), rfl, rfl, rfl, by norm_num⟩
    · rfl
  have hr : Reduced₂ [(true, i), (false, i)] [.cap 0] := by
    change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag
    simp
  have hs : IsMatching₂ [(false, i)] [(false, i)] [] := ⟨trivial, rfl⟩
  have hrs : Reduced₂ [(false, i)] [] := by
    change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag
    simp
  have hi : Iso (pairing₂ [(false, i)] [])
      (pairing₂ [(true, i), (false, i)] [.cap 0]) := by
    change Iso [(0, (true, i)), (0, (false, i))]
      [(2, (true, i)), (2, (false, i))]
    exact (Chord.iso_map_of_injOn [(0, (true, i)), (0, (false, i))]
      (fun n => n + 2) (by intro x _ y _ h; omega)).symm
  exact cupAttach_normalized_degree_parity D sy μ hm hr hs hrs hi

/-- Odd-colour concrete instance of the cap-to-zigzag normalization. -/
theorem odd_cap_zigzag_normalization :
    tableDegree PositivePointGradingExamples.twoColourDatum
      PositivePointGradingExamples.twoColourSymmetrizer 0
      (tLay [(false, false)] []) =
    tableDegree PositivePointGradingExamples.twoColourDatum
      PositivePointGradingExamples.twoColourSymmetrizer 0
      (tLay [(false, false)] [.mv (.cup 0 (false, false)), .cap 1]) ∧
    xpar PositivePointGradingExamples.twoColourDatum 0 (tLay [(false, false)] []) =
    xpar PositivePointGradingExamples.twoColourDatum 0
      (tLay [(false, false)] [.mv (.cup 0 (false, false)), .cap 1]) :=
  cap_zigzag_normalization PositivePointGradingExamples.twoColourDatum
    PositivePointGradingExamples.twoColourSymmetrizer false 0

end OddMath.SKM.TwoSidedGradingExamples
