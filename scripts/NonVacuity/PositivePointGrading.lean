import OddMath

/-! Non-vacuity checks in `NonVacuity.PositivePointGrading`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.PositivePointGrading

open OddMath.SKM StringDiagrams StringDiagrams.Chord DTMove
open OddMath.SKM.PositivePointGradingExamples

-- Both distinct-colour point placements, with every hypothesis proved.
example :
    ∀ ds ∈ [[.dt 0, .tm (.mv (.cross 0))], [.tm (.mv (.cross 0)), .dt 1]],
    ∃ (L : List (LayerData Bool))
      (hL : SChain [(true, false), (true, true)] L [(true, true), (true, false)]),
      L.map ofL = dLay [(true, false), (true, true)] ds ∧
      Diagram.degree (gdeg twoColourDatum twoColourSymmetrizer)
        (mkD twoColourDatum 0 L hL) = 2 ∧
      xpar twoColourDatum 0 (dLay [(true, false), (true, true)] ds) = 1 :=
  two_colour_point_invariance

end NonVacuity.PositivePointGrading
