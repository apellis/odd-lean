import OddMath

/-! Non-vacuity checks in `NonVacuity.DecoratedNormalization`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.DecoratedNormalization
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositivePointGradingExamples

example : tableDegree twoColourDatum twoColourSymmetrizer 0
    (dLay [(true, false)] [.tm (.mv (.cup 1 (false, false))), .dt 1, .tm (.cap 0)]) = 2 ∧
    xpar twoColourDatum 0
      (dLay [(true, false)] [.tm (.mv (.cup 1 (false, false))), .dt 1, .tm (.cap 0)]) = 1 :=
  DecoratedNormalizationExamples.odd_internal_cup_cap_normalized_dot

example : tableDegree twoColourDatum twoColourSymmetrizer 0
    (dLay [(true, false), (false, false)] [.dt 1, .tm (.cap 0)]) +
      twoColourSymmetrizer.d false *
        (1 + twoColourDatum.h false (wt twoColourDatum 0 [(false, false)])) = 2 ∧
    xpar twoColourDatum 0 (dLay [(true, false), (false, false)] [.dt 1, .tm (.cap 0)]) = 1 :=
  DecoratedNormalizationExamples.odd_right_cup_cap_normalized_dot

example :
    let A : List (Letter Bool) := [(true, false)]
    let R : List (TMove (Letter Bool)) := [.mv (.cup 1 (false, false)), .cap 0]
    let T := tRun flipL A.length (tStart A) (R.take 1)
    idD T.st (A.length + 1) = 2 ∧ tRen A.length T (R.drop 1) 2 = 0 :=
  DecoratedNormalizationExamples.internal_cup_cap_renaming false

end NonVacuity.DecoratedNormalization
