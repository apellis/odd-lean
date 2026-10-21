import OddMath

/-! Non-vacuity checks in `NonVacuity.CapDotGrading`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.CapDotGrading
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositivePointGradingExamples
open OddMath.SKM.CapPushGradingExamples

-- The crossing bound is forced to equality, so both numeric conclusions are used.
example : ∃ E' : List (Move (Letter Bool)),
    Fits 0 E' ∧ Iso (run flipL E') zigzagPairing ∧ E' ≠ [] ∧ ncr E' = 1 ∧
      tableDegree twoColourDatum twoColourSymmetrizer 0 zigzagSource =
        tableDegree twoColourDatum twoColourSymmetrizer 0 (chordLay [] E') ∧
      xpar twoColourDatum 0 zigzagSource = xpar twoColourDatum 0 (chordLay [] E') :=
  zigzag_cap_push

-- The downward dot lies on a fresh cup leg, renamed by the following cap.
example : tableDegree twoColourDatum twoColourSymmetrizer 0
    (dLay [(true, false)] [.tm (.mv (.cup 1 (false, false))), .dt 1, .tm (.cap 0)]) = 2 ∧
    xpar twoColourDatum 0
      (dLay [(true, false)] [.tm (.mv (.cup 1 (false, false))), .dt 1, .tm (.cap 0)]) = 1 :=
  MixedDotGradingExamples.internal_cup_cap_dot twoColourDatum twoColourSymmetrizer 0 false

example :
    let A : List (Letter Bool) := [(true, false)]
    let R : List (TMove (Letter Bool)) := [.mv (.cup 1 (false, false)), .cap 0]
    let T := tRun flipL A.length (tStart A) (R.take 1)
    idD T.st (A.length + 1) = 2 ∧ tRen A.length T (R.drop 1) 2 = 0 :=
  MixedDotGradingExamples.internal_cup_cap_renaming false

end NonVacuity.CapDotGrading
