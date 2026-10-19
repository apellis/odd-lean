import OddMath.SKM.LeftCupAttachment
import OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples

/-! Nonempty odd-root consumer through the literal-downward-attachment headline.
The old matching creates a fresh strand, dots it, then merges its ID by an internal cap.
At rightmost weight 2 the added left cup has degree -1 and parity 1. -/
namespace OddMath.SKM.LeftCupAttachmentExamples
open StringDiagrams StringDiagrams.Chord DTMove CoveringQuantum
open PositiveDecoratedFamilyCoefficientsExamples (oddDatum)

private abbrev A : List (Letter Unit) := [(false, ())]
private abbrev R : List (TMove (Letter Unit)) := [.mv (.cup 1 (true, ())), .cap 0]
private abbrev ds : List (DTMove Unit) := [.tm (.mv (.cup 1 (true, ()))), .dt 2, .tm (.cap 0)]
private def q (_ : ℕ) : ℕ × ℕ := (1, 2)
private def c (_ : MatchingStrand A R) : ℕ := 1

private theorem matching : IsMatching₂ A A R := by
  constructor
  · refine ⟨by change 2 ≤ 2; decide, ?_⟩
    refine ⟨?_, trivial⟩
    exact ⟨(0, (false, ())), (2, (true, ())), rfl, rfl, rfl, by decide⟩
  · rfl

private theorem ends : leftEnds₂ A R = [0] := by
  have h (j : ℕ) : IsLeftEnd (pairing₂ A R) j ↔ j = 0 := by
    change (j < 2 ∧ ¬ ∃ k, k < j ∧ Same [(0, (true, ())), (0, (false, ()))] j k) ↔ j = 0
    constructor
    · intro h
      have hj := h.1
      interval_cases j
      · rfl
      · exact (h.2 ⟨0, by decide, by simp [Same, idAt]⟩).elim
    · rintro rfl
      exact ⟨by decide, by simp⟩
  unfold leftEnds₂
  simp only [show (pairing₂ A R).length = 2 from rfl, h]
  decide

private theorem points : ∀ j ∈ leftEnds₂ A R,
    (q j).1 ≤ R.length ∧ OnStrand₂ A R j (q j) := by
  intro j hj
  rw [ends] at hj
  obtain rfl := List.mem_singleton.mp hj
  change 1 ≤ 2 ∧ 2 < 3 ∧ 0 = 0
  decide

private theorem decoration : Decorates₂ A R q (strandCounts c) ds := by
  constructor
  · rfl
  · simp [dotPts, ends, strandCounts, c, q]

private theorem reduced : Reduced₂ A R := by
  constructor
  · exact List.nodup_nil
  · intro z hz
    change z ∈ ([] : List (Sym2 ℕ)) at hz
    exact False.elim (List.not_mem_nil hz)

/-- Both counters and the cap renaming are nontrivial: the old fresh ID is 2,
the attached fresh ID is 1, and both are merged into ID 0 by the subsequent cap. -/
theorem internal_cap_fresh_ids :
    let T := tRun flipL 1 (tStart A) (R.take 1)
    let U := tRun flipL 0 (tStart ([] : List (Letter Unit)))
      ((leftCupAttachMatching () R).take 2)
    T.nxt = 3 ∧ U.nxt = 2 ∧ idD T.st 3 = 2 ∧ idD U.st 3 = 1 ∧
      tRen 1 T (R.drop 1) 2 = 0 ∧
      tRen 0 U ((leftCupAttachMatching () R).drop 2) 1 = 0 := by
  decide

/-- All transport conclusions are obtained from the new headline, including the dot
before an internal cap. The q-shift is negative and the parity changes by one. -/
theorem internal_cap_odd_shift :
    IsMatching₂ [] [(true, ()), (false, ())] (leftCupAttachMatching () R) ∧
    Iso (pairing₂ [] (leftCupAttachMatching () R)) (pairing₂ A R) ∧
    Reduced₂ [] (leftCupAttachMatching () R) ∧
    ∃ e : MatchingStrand A R ≃ MatchingStrand [] (leftCupAttachMatching () R),
      (∀ j, (e j).val = j.val) ∧
      Decorates₂ [] (leftCupAttachMatching () R) (cupAttachPoint ∘ q)
        (strandCounts (c ∘ e.symm)) (leftCupAttachMoves () ds) ∧
      OnStrand₂ [] (leftCupAttachMatching () R) 0 (2, 3) ∧
      (2 : ℕ) ≤ (leftCupAttachMatching () R).length ∧
      tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2
        (dLay [] (leftCupAttachMoves () ds)) =
        tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 2 (dLay A ds) - 1 ∧
      xpar oddDatum.toSKM 2 (dLay [] (leftCupAttachMoves () ds)) =
        xpar oddDatum.toSKM 2 (dLay A ds) + 1 := by
  obtain ⟨hm, hi, hr, e, hev, ht⟩ :=
    cup_attach_down_decorated oddDatum.toSKM oddDatum.skmSymmetrizer 2 matching
  obtain ⟨hq, hdec, hd, hp⟩ := ht q points c ds decoration
  have hj : 0 ∈ leftEnds₂ [] (leftCupAttachMatching () R) := by
    change 0 ∈ leftEnds₂ [] (CupAttachment.cupAttachMatching true () R)
    rw [CupAttachment.leftEnds₂_cupAttach (o := true) matching]
    change 0 ∈ leftEnds₂ A R
    rw [ends]
    exact List.mem_singleton_self _
  refine ⟨hm, hi, hr reduced, e, hev, hdec, (hq 0 hj).2, (hq 0 hj).1, ?_, ?_⟩
  · have hdeg : oddDatum.skmSymmetrizer.d () *
        (1 - oddDatum.toSKM.h () (wt oddDatum.toSKM 2 [])) = -1 := by decide
    rw [hdeg] at hd
    simpa only [sub_eq_add_neg] using hd
  · have hpar : ipar oddDatum.toSKM () (wt oddDatum.toSKM 2 []) = 1 := by decide
    simpa only [hpar] using hp


end OddMath.SKM.LeftCupAttachmentExamples
