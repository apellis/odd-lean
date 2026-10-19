import OddMath.SKM.CapPushGrading
import OddMath.SKM.PositivePointGradingExamples

/-! A nonempty cap-push example whose interleaved pairing forces a sharp crossing bound. -/

namespace OddMath.SKM.CapPushGradingExamples
open StringDiagrams
open StringDiagrams.Chord (Move Fits run Iso rl)
open PositivePointGradingExamples

/-- Three odd-colour cups; the last creates the left end of the cap. -/
def zigzagInput : List (Move (Letter Bool)) :=
  [.cup 0 (true, false), .cup 0 (true, false), .cup 1 (true, false)]

def zigzagPairing : List (ℕ × Letter Bool) :=
  [(2, (true, false)), (4, (true, false)), (2, (false, false)), (4, (false, false))]

def zigzagSource : List (XLayer Bool) :=
  chordLay [] zigzagInput ++
    (capBlk [(false, false)] (true, false) 0).map
      (xwhL [(true, false), (true, false)] [(false, false)])

/-- The surviving pairing interleaves, so the crossing-bound equality cannot be vacuous. -/
theorem zigzag_pairing_crossing : 0 < Chord.cr zigzagPairing := by
  apply Finset.card_pos.mpr
  refine ⟨(0, 1, 2, 3), Chord.mem_crSet.mpr ?_⟩
  norm_num [Chord.Cr4, Chord.Same, Chord.idAt, zigzagPairing]

/-- Fully discharged cap-push with nonempty middle block and four output endpoints. -/
theorem zigzag_cap_push : ∃ E' : List (Move (Letter Bool)),
    Fits 0 E' ∧ Iso (run flipL E') zigzagPairing ∧ E' ≠ [] ∧ ncr E' = 1 ∧
      tableDegree twoColourDatum twoColourSymmetrizer 0 zigzagSource =
        tableDegree twoColourDatum twoColourSymmetrizer 0 (chordLay [] E') ∧
      xpar twoColourDatum 0 zigzagSource = xpar twoColourDatum 0 (chordLay [] E') := by
  have hf : Fits 0 zigzagInput := by simp [zigzagInput, Fits, Move.Ok, Move.len]
  obtain ⟨E', hf', hi, hn, he⟩ := numericCapPush twoColourDatum twoColourSymmetrizer 0
    zigzagInput hf [(2, (true, false)), (4, (true, false))] [(2, (false, false))]
      [(0, (false, false))] (4, (false, false)) (0, (true, false)) (by decide) rfl (by decide)
  have hi' : Iso (run flipL E') zigzagPairing := by
    simpa [rl, Chord.rlId, zigzagPairing] using hi
  have hn' : ncr E' ≤ 1 := by simpa [zigzagInput] using hn
  have hc := Chord.cr_run_le_ncr (d := flipL) hf'
  have hc' := Chord.cr_le_of_iso hi'.symm
  have hpos := zigzag_pairing_crossing
  have heq : ncr E' = 1 := by omega
  have he' := he (by simpa [zigzagInput] using heq)
  refine ⟨E', hf', hi', ?_, heq, ?_⟩
  · intro hz
    have hlen := hi'.length_eq
    simp [hz, Chord.run, zigzagPairing] at hlen
  · simpa [zigzagSource] using he'

end OddMath.SKM.CapPushGradingExamples
