import OddMath.SKM.CupAttachmentReduced

namespace OddMath.SKM.CupReducedExamples
open StringDiagrams StringDiagrams.Chord

/-- The nonempty repeated-colour crossing retains its single crossing after attachment. -/
theorem crossing_cup :
    let R : List (TMove (Letter Unit)) := [.mv (.cross 0)]
    let a : List (Letter Unit) := [(true, ())]
    IsMatching₂ a [(false, ()), (true, ()), (true, ())] (cupAttachMatching () R) ∧
      Reduced₂ a (cupAttachMatching () R) ∧ ncr₂ (cupAttachMatching () R) = 1 := by
  dsimp only
  have hm : IsMatching₂ [(true, ()), (true, ())] [(true, ()), (true, ())]
      [.mv (.cross 0)] := by
    constructor
    · change 3 < 4 ∧ True
      decide
    · rfl
  have hr : Reduced₂ [(true, ()), (true, ())] [.mv (.cross 0)] := by
    change [s(2, 0)].Nodup ∧ ∀ z ∈ [s(2, 0)], ¬ z.IsDiag
    simp
  exact ⟨(cupAttach_matching_iso hm).1, reduced₂_cupAttach hm hr,
    (ncr₂_cupAttachMatching () _).trans rfl⟩

/-- A cap becomes a literal cup-cap zigzag; crossing-minimality still holds. -/
theorem cap_attached_zigzag :
    cupAttachMatching () ([.cap 0] : List (TMove (Letter Unit))) =
      [.mv (.cup 0 (false, ())), .cap 1] ∧
    IsMatching₂ [(false, ())] [(false, ())]
      [.mv (.cup 0 (false, ())), .cap 1] ∧
    Reduced₂ [(false, ())] [.mv (.cup 0 (false, ())), .cap 1] := by
  have hm : IsMatching₂ [(true, ()), (false, ())] [] [.cap 0] := by
    constructor
    · refine ⟨?_, trivial⟩
      exact ⟨(2, (true, ())), (0, (false, ())), rfl, rfl, rfl, by decide⟩
    · rfl
  have hr : Reduced₂ [(true, ()), (false, ())] [.cap 0] := by
    change ([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag
    simp
  exact ⟨rfl, (cupAttach_matching_iso hm).1, reduced₂_cupAttach hm hr⟩

end OddMath.SKM.CupReducedExamples
