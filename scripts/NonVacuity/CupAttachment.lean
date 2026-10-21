import OddMath

/-! Non-vacuity checks in `NonVacuity.CupAttachment`.
Conventions are in `scripts/NonVacuity.lean`. -/

open CategoryTheory

noncomputable section

namespace NonVacuity.CupAttachment
open OddMath.SKM StringDiagrams StringDiagrams.Chord DTMove
open OddMath.SKM.PositiveFormCoefficientsExamples
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples

private def R : List (TMove (Letter Unit)) := [.mv (.cross 0)]
private def A : List (Letter Unit) := [(true, ()), (true, ())]
private def a : List (Letter Unit) := [(true, ())]
private def ds : List (DTMove Unit) := [.dt 0, .tm (.mv (.cross 0))]
private def q (j : ℕ) : ℕ × ℕ := (0, 1 - j)
private def c (j : MatchingStrand A R) : ℕ := if j.val = 1 then 1 else 0

example :
    IsMatching₂ a ((false, ()) :: A) (cupAttachMatching () R) ∧
    ∃ e : MatchingStrand A R ≃ MatchingStrand a (cupAttachMatching () R),
      (∀ j, (e j).val = j.val) ∧
      Decorates₂ a (cupAttachMatching () R) (cupAttachPoint ∘ q)
        (strandCounts (c ∘ e.symm)) (cupAttachMoves () ds) ∧
      (∀ j ∈ leftEnds₂ a (cupAttachMatching () R),
        (cupAttachPoint (q j)).1 ≤ (cupAttachMatching () R).length ∧
        OnStrand₂ a (cupAttachMatching () R) j (cupAttachPoint (q j))) ∧
      ∃ (L : List (LayerData Unit))
        (hLB : SChain a (cupAttachLayers () a L) ((false, ()) :: A)),
        (cupAttachLayers () a L).map ofL = dLay a (cupAttachMoves () ds) ∧
        Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
          (mkD oddDatum.toSKM 0 (cupAttachLayers () a L) hLB) =
          oddDatum.skmSymmetrizer.d () * oddDatum.toSKM.d () () +
            2 * oddDatum.skmSymmetrizer.d () +
            oddDatum.skmSymmetrizer.d () * (1 + oddDatum.toSKM.h () (wt oddDatum.toSKM 0 a)) ∧
        xpar oddDatum.toSKM 0 (dLay a (cupAttachMoves () ds)) =
          oddDatum.toSKM.parity () * oddDatum.toSKM.parity () + oddDatum.toSKM.parity () :=
  CupTransportExamples.crossing_dot_cup oddDatum.toSKM oddDatum.skmSymmetrizer 0

example :
    let S : List (TMove (Letter Unit)) := [.mv (.cup 1 (false, ())), .cap 0]
    IsMatching₂ [] [(false, ()), (true, ())] (cupAttachMatching () S) ∧
    OnStrand₂ [] (cupAttachMatching () S) 0 (2, 3) := CupTransportExamples.cup_cap_point

example :
    ∀ ds ∈ [[.dt 0, .tm (.mv (.cross 0))], [.tm (.mv (.cross 0)), .dt 1]],
    ∃ (L : List (LayerData Unit))
      (hL : SChain [(true, ()), (true, ())] L [(true, ()), (true, ())])
      (hB : SChain [(true, ())] (cupAttachLayers () [(true, ())] L)
        [(false, ()), (true, ()), (true, ())]),
      L.map ofL = dLay [(true, ()), (true, ())] ds ∧
      (cupAttachLayers () [(true, ())] L).map ofL = dLay [(true, ())] (cupAttachMoves () ds) ∧
      Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
        (mkD oddDatum.toSKM 0 L hL) =
        oddDatum.skmSymmetrizer.d () * oddDatum.toSKM.d () () +
          2 * oddDatum.skmSymmetrizer.d () ∧
      Diagram.degree (gdeg oddDatum.toSKM oddDatum.skmSymmetrizer)
        (mkD oddDatum.toSKM 0 (cupAttachLayers () [(true, ())] L) hB) =
        oddDatum.skmSymmetrizer.d () * oddDatum.toSKM.d () () +
          2 * oddDatum.skmSymmetrizer.d () + oddDatum.skmSymmetrizer.d () *
          (1 + oddDatum.toSKM.h () (wt oddDatum.toSKM 0 [(true, ())])) ∧
      xpar oddDatum.toSKM 0 (dLay [(true, ())] (cupAttachMoves () ds)) =
        oddDatum.toSKM.parity () * oddDatum.toSKM.parity () + oddDatum.toSKM.parity () :=
  cup_attached_crossing_dot_points oddDatum.toSKM oddDatum.skmSymmetrizer 0 () ()

end NonVacuity.CupAttachment
