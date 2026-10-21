import OddMath

/-! Non-vacuity checks in `NonVacuity.BoundaryCrossing`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.BoundaryCrossing
open StringDiagrams StringDiagrams.Chord OddMath.SKM MixedCrossingLocalExamples

example : tableDegree oddDatum oddSymmetrizer 0 (tLay B S) =
    tableDegree oddDatum oddSymmetrizer 0 (tLay A R) ∧
    xpar oddDatum 0 (tLay B S) = xpar oddDatum 0 (tLay A R) + 1 :=
  BoundaryNormalizationExamples.existing_intersection_normalized

example : ∃ (A B : List (Letter Bool)) (R S : List (StringDiagrams.Chord.TMove (Letter Bool))),
    tableDegree oddDatum oddSymmetrizer 0 (tLay B S) =
      tableDegree oddDatum oddSymmetrizer 0 (tLay A R) ∧
    xpar oddDatum 0 (tLay B S) = xpar oddDatum 0 (tLay A R) + 1 :=
  ⟨_, _, _, _, BoundaryNormalizationExamples.no_intersection_normalized⟩

example : ∃ (qR qS : ℕ → ℕ × ℕ)
    (cR : MatchingStrand A R → ℕ) (cS : MatchingStrand B S → ℕ),
    (∀ j ∈ leftEnds₂ A R, (qR j).1 ≤ R.length ∧ OnStrand₂ A R j (qR j)) ∧
    (∀ j ∈ leftEnds₂ B S, (qS j).1 ≤ S.length ∧ OnStrand₂ B S j (qS j)) ∧
    Decorates₂ A R qR (strandCounts cR) sourceDots ∧
    Decorates₂ B S qS (strandCounts cS) targetDots ∧
    tableDegree oddDatum oddSymmetrizer 0 (dLay B targetDots) = 5 ∧
    tableDegree oddDatum oddSymmetrizer 0 (dLay A sourceDots) = 5 ∧
    xpar oddDatum 0 (dLay B targetDots) = 0 ∧
    xpar oddDatum 0 (dLay A sourceDots) = 1 :=
  ⟨_, _, _, _, BoundaryNormalizationExamples.finite_dotted_normalization⟩

example : (1 : ℚ) ^ (xpar oddDatum 0 (dLay A sourceDots)).val = 1 ∧
    (-1 : ℚ) ^ (xpar oddDatum 0 (dLay A sourceDots)).val = -1 ∧
    (-1 : ℚ) ^ (xpar oddDatum 0 (dLay B targetDots)).val = 1 :=
  signs_detect_factor

end NonVacuity.BoundaryCrossing
