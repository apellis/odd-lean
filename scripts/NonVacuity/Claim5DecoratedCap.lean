import OddMath

/-! Non-vacuity checks in `NonVacuity.Claim5DecoratedCap`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.Claim5DecoratedCap
open StringDiagrams StringDiagrams.Chord OddMath.SKM
open MixedCrossingLocalExamples (oddDatum oddSymmetrizer)

-- The closed family consumer supplies both finite fibres and the actual restricted map.
example (ε k : Bool) := CapDecoratedNormalizationExamples.family_fibres ε k

-- Two cap dots and three surviving odd dots at the shifted physical suffix weight.
example : ∃ ds es : List (DTMove Bool),
    tableDegree oddDatum oddSymmetrizer 0
      (dLay [(true, false), (true, false), (false, false), (false, false)] ds) = 14 ∧
    xpar oddDatum 0
      (dLay [(true, false), (true, false), (false, false), (false, false)] ds) = 1 ∧
    tableDegree oddDatum oddSymmetrizer 0
      (dLay [(true, false), (false, false), (true, false), (false, false)] es) = 10 ∧
    xpar oddDatum 0
      (dLay [(true, false), (false, false), (true, false), (false, false)] es) = 0 :=
  ⟨_, _, CapDecoratedNormalizationExamples.nonempty_values⟩

example (ε : Bool) := CapDecoratedNormalizationExamples.nonzero_label_values ε

end NonVacuity.Claim5DecoratedCap
