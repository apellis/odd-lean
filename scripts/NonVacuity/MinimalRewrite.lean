import OddMath

/-! Non-vacuity checks in `NonVacuity.MinimalRewrite`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.MinimalRewrite
open OddMath.SKM StringDiagrams StringDiagrams.Chord
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples

example :
    let R : List (TMove (Letter Unit)) := [.mv (.cross 0)]
    let a : List (Letter Unit) := [(true, ())]
    IsMatching₂ a [(false, ()), (true, ()), (true, ())] (cupAttachMatching () R) ∧
      Reduced₂ a (cupAttachMatching () R) ∧ ncr₂ (cupAttachMatching () R) = 1 :=
  CupReducedExamples.crossing_cup

example :
    cupAttachMatching () ([.cap 0] : List (TMove (Letter Unit))) =
      [.mv (.cup 0 (false, ())), .cap 1] ∧
    IsMatching₂ [(false, ())] [(false, ())]
      [.mv (.cup 0 (false, ())), .cap 1] ∧
    Reduced₂ [(false, ())] [.mv (.cup 0 (false, ())), .cap 1] :=
  CupReducedExamples.cap_attached_zigzag

example :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
      (chordLay [(false, ())] [.cup 0 (true, ()), .cross 1]) =
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
      (chordLay [(false, ())] [.cup 1 (true, ()), .cross 0]) ∧
    xpar oddDatum.toSKM 0 (chordLay [(false, ())] [.cup 0 (true, ()), .cross 1]) =
      xpar oddDatum.toSKM 0 (chordLay [(false, ())] [.cup 1 (true, ()), .cross 0]) :=
  TableIsotopyExamples.pitchfork oddDatum.toSKM oddDatum.skmSymmetrizer 0 (true, ()) (false, ())

example :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
      (chordLay [] [.cup 0 (false, ()), .cup 0 (true, ()), .cross 1]) =
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
      (chordLay [] [.cup 0 (false, ()), .cup 1 (true, ()), .cross 0]) ∧
    xpar oddDatum.toSKM 0 (chordLay [] [.cup 0 (false, ()), .cup 0 (true, ()), .cross 1]) =
      xpar oddDatum.toSKM 0 (chordLay [] [.cup 0 (false, ()), .cup 1 (true, ()), .cross 0]) :=
  TableIsotopyExamples.contextual_pitchfork oddDatum.toSKM oddDatum.skmSymmetrizer 0 () ()

example :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0 ((crossL [] () () []).map ofL) =
      Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
        (mkD oddDatum.toSKM 0 (crossL [] () () [])
          (show SChain [up (), up ()] (crossL [] () () []) [up (), up ()] from ⟨rfl, rfl⟩)) ∧
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0 ((crossL [] () () []).map ofL) =
      oddDatum.skmSymmetrizer.d () * oddDatum.toSKM.d () () :=
  TableIsotopyExamples.ordinary_crossing oddDatum.toSKM oddDatum.skmSymmetrizer 0 () ()

example (μ : ℤ) :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer μ [([], .lcup (), [])] =
      if 0 < oddDatum.toSKM.h () μ then
        gsum oddDatum.toSKM oddDatum.skmSymmetrizer μ (dcupL () (oddDatum.toSKM.h () μ - 1).toNat)
      else gsum oddDatum.toSKM oddDatum.skmSymmetrizer μ
        (etaL () (-oddDatum.toSKM.h () μ).toNat ++ lcrossL () ()) :=
  tableDegree_etaP_source oddDatum.toSKM oddDatum.skmSymmetrizer μ ()

example (μ : ℤ) :
    tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer μ [([], .lcap (), [])] =
      if oddDatum.toSKM.h () μ < 0 then
        gsum oddDatum.toSKM oddDatum.skmSymmetrizer μ (dcapL () (-oddDatum.toSKM.h () μ - 1).toNat)
      else gsum oddDatum.toSKM oddDatum.skmSymmetrizer μ
        (lcrossL () () ++ epsL () (oddDatum.toSKM.h () μ).toNat) :=
  tableDegree_epsP_source oddDatum.toSKM oddDatum.skmSymmetrizer μ ()

end NonVacuity.MinimalRewrite
