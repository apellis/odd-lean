import OddMath

/-! Non-vacuity checks in `NonVacuity.LeftCupNormalization`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.LeftCupNormalization
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples (oddDatum)

private abbrev A : List (Letter Unit) := [(false, ())]
private abbrev R : List (TMove (Letter Unit)) := [.mv (.cup 1 (true, ())), .cap 0]
private abbrev ds : List (DTMove Unit) := [.tm (.mv (.cup 1 (true, ()))), .dt 2, .tm (.cap 0)]
private abbrev es : List (DTMove Unit) := [.tm (.mv (.cup 0 (true, ()))), .dt 0]

example :
    let T := tRun flipL 1 (tStart A) (R.take 1)
    let U := tRun flipL 0 (tStart ([] : List (Letter Unit)))
      ((leftCupAttachMatching () R).take 2)
    T.nxt = 3 ∧ U.nxt = 2 ∧ idD T.st 3 = 2 ∧ idD U.st 3 = 1 ∧
      tRen 1 T (R.drop 1) 2 = 0 ∧
      tRen 0 U ((leftCupAttachMatching () R).drop 2) 1 = 0 :=
  LeftCupAttachmentExamples.internal_cap_fresh_ids

example :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2
      (dLay [] (leftCupAttachMoves () ds)) =
      tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2 (dLay A ds) - 1 ∧
    xpar oddDatum.toSKM 2 (dLay [] (leftCupAttachMoves () ds)) =
      xpar oddDatum.toSKM 2 (dLay A ds) + 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, hd, hp⟩ := LeftCupAttachmentExamples.internal_cap_odd_shift
  exact ⟨hd, hp⟩

example :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2 (dLay [] es) =
      tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2 (dLay A ds) - 1 ∧
    xpar oddDatum.toSKM 2 (dLay [] es) = xpar oddDatum.toSKM 2 (dLay A ds) + 1 :=
  LeftCupNormalizationExamples.normalized_internal_cap_odd_shift

example : tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2 (dLay [] es) = 1 ∧
    xpar oddDatum.toSKM 2 (dLay [] es) = 0 := by
  obtain ⟨_, _, _, _, _, _, _, hd, hp⟩ :=
    LeftCupNormalizationExamples.normalized_internal_cap_values
  exact ⟨hd, hp⟩

end NonVacuity.LeftCupNormalization
