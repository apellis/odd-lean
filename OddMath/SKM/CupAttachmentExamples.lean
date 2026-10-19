import OddMath.SKM.CupAttachment
import OddMath.SKM.PositivePointGradingExamples

/-! Nonempty repeated-colour crossing with a dot below the crossing, exercising
literal cup attachment, finite strand counts, distinguished points and actual grading. -/
namespace OddMath.SKM.CupTransportExamples
open StringDiagrams StringDiagrams.Chord DTMove

private def R : List (TMove (Letter Unit)) := [.mv (.cross 0)]
private def A : List (Letter Unit) := [(true, ()), (true, ())]
private def a : List (Letter Unit) := [(true, ())]
private def ds : List (DTMove Unit) := [.dt 0, .tm (.mv (.cross 0))]
private def q (j : ℕ) : ℕ × ℕ := (0, 1 - j)
private def c (j : MatchingStrand A R) : ℕ := if j.val = 1 then 1 else 0

private theorem matching : IsMatching₂ A A R := by
  constructor
  · change 3 < 4 ∧ True
    decide
  · rfl

private theorem ends : leftEnds₂ A R = [0, 1] := by
  have h (j : ℕ) : IsLeftEnd (pairing₂ A R) j ↔ j < 2 :=
    mem_leftEnds₂.symm.trans
      (positive_mem_leftEnds₂ (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ()) matching j)
  unfold leftEnds₂
  simp only [show (pairing₂ A R).length = 4 from rfl, h]
  decide

private theorem points : ∀ j ∈ leftEnds₂ A R,
    (q j).1 ≤ R.length ∧ OnStrand₂ A R j (q j) := by
  intro j hj
  rw [ends] at hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · change 0 ≤ 1 ∧ 1 < 2 ∧ 0 = 0
    decide
  · change 0 ≤ 1 ∧ 0 < 2 ∧ 2 = 2
    decide

private theorem decoration : Decorates₂ A R q (strandCounts c) ds := by
  constructor
  · rfl
  · simp only [ds, dotPts, ends, List.flatMap_cons, List.flatMap_nil, strandCounts]
    simp [c, q]

/-- A genuine nonempty consumer of the full literal attachment conjunction. -/
theorem crossing_dot_cup {X : Type*} [AddCommGroup X]
    (D : Datum Unit X) (sy : Symmetrizer D) (μ : X) :
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
        Diagram.degree (gdeg D sy) (mkD D μ (cupAttachLayers () a L) hLB) =
          sy.d () * D.d () () + 2 * sy.d () + sy.d () * (1 + D.h () (wt D μ a)) ∧
        xpar D μ (dLay a (cupAttachMoves () ds)) =
          D.parity () * D.parity () + D.parity () := by
  obtain ⟨hm, _, e, hev, ht⟩ := cup_attach_up_decorated D sy μ matching
  obtain ⟨L, hL, he, hd, hp⟩ := PositivePointGradingExamples.crossing_dot_points D sy μ () () ds
    (by exact List.mem_cons_self)
  obtain ⟨hq, hdec, hLB, hmap, hdeg, hpar⟩ := ht q points c ds decoration L hL he
  exact ⟨hm, e, hev, hdec, hq, L, hLB, hmap, by rw [hd] at hdeg; exact hdeg, hpar.trans hp⟩

/-- An old internal cup and cap exercise the fresh-ID offset and cap renaming. -/
theorem cup_cap_point :
    let S : List (TMove (Letter Unit)) := [.mv (.cup 1 (false, ())), .cap 0]
    IsMatching₂ [] [(false, ()), (true, ())] (cupAttachMatching () S) ∧
    OnStrand₂ [] (cupAttachMatching () S) 0 (2, 3) := by
  dsimp only
  have hm : IsMatching₂ [(true, ())] [(true, ())]
      [.mv (.cup 1 (false, ())), .cap 0] := by
    constructor
    · refine ⟨by change 2 ≤ 2; decide, ?_⟩
      refine ⟨?_, trivial⟩
      refine ⟨(0, (true, ())), (2, (false, ())), rfl, rfl, rfl, by decide⟩
    · rfl
  have hp : OnStrand₂ [(true, ())] [.mv (.cup 1 (false, ())), .cap 0] 0 (1, 2) := by
    change 2 < 3 ∧ 0 = 0
    decide
  exact ⟨(cupAttach_matching_iso hm).1, (onStrand₂_cupAttach hm (by decide) hp).2⟩

end OddMath.SKM.CupTransportExamples
