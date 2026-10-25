import OddMath.SKM.CupCompletedChoice

/-! Complete cup-adapted choices with nonempty contexts and a repeated colour. -/
noncomputable section
namespace OddMath.SKM.CupCompletedChoiceExamples
open StringDiagrams StringDiagrams.Chord

private abbrev P : List (Letter Bool) := [up false]
private abbrev Q : List (Letter Bool) := [dn true]
private abbrev a : List (Letter Bool) := P ++ Q

/-- All construction hypotheses are discharged; arbitrary cup dot counts and
all residual decorations are retained in one complete family. -/
theorem complete_paired_sector (ε : Bool) :
    ∃ (G : MatchingBasisChoice a (P ++ Q))
      (F : MatchingBasisChoice a (P ++ (ε, false) :: (!ε, false) :: Q))
      (p : ℕ × G.Labels ↪ F.Labels),
      ∀ b (j : G.members) n, F.layers (p (b, ⟨j, n⟩)) =
        (PointedMatching.ofStrict (G.matching j j.property).1
          (G.matching j j.property).2).layers n ++
        (xCupL (ε, false)).map (xwhL P Q) ++
        dLay (P ++ (ε, false) :: (!ε, false) :: Q)
          (List.replicate b (.dt (if ε then P.length else P.length + 1))) := by
  obtain ⟨B⟩ := MatchingBasisChoice.nonempty a (P ++ (ε, false) :: (!ε, false) :: Q)
  obtain ⟨G⟩ := MatchingBasisChoice.nonempty a (P ++ Q)
  obtain ⟨F, e, he⟩ := exists_choice_with_literal_cups a P Q ε false B G
  let p : ℕ × G.Labels ↪ F.Labels :=
    ⟨fun z => e (.inr z), e.injective.comp Sum.inr_injective⟩
  exact ⟨G, F, p, he⟩

#print axioms exists_cup_completed_choice
#print axioms exists_choice_with_literal_cups
#print axioms complete_paired_sector
end OddMath.SKM.CupCompletedChoiceExamples
