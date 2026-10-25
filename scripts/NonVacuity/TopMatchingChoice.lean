import OddMath.SKM.TopMatchingChoice

/-! Bounded multiplicities and top serializers on two upward colours. -/
noncomputable section
namespace NonVacuity.TopMatchingChoice
open StringDiagrams StringDiagrams.Chord OddMath.SKM
private def colour : Fin 2 → Bool := ![false, true]
private def word : List (Letter Bool) := List.ofFn fun r => (true, colour r)
private def F : MatchingBasisChoice word word := Classical.choice (MatchingBasisChoice.nonempty word word)

theorem two_position_counts :
    (TopCounts.ofFn (![2, 3] : Fin 2 → ℕ)).val 0 = 2 ∧
      (TopCounts.ofFn (![2, 3] : Fin 2 → ℕ)).val 1 = 3 := by
  constructor
  · exact TopCounts.ofFn_apply (![2, 3] : Fin 2 → ℕ) ⟨0, by decide⟩
  · exact TopCounts.ofFn_apply (![2, 3] : Fin 2 → ℕ) ⟨1, by decide⟩

theorem every_top_count_realized (R : F.members) (n : TopCounts 2) :
    ∃ m, F.topCountsEquiv colour colour R m = n :=
  (F.topCountsEquiv colour colour R).surjective n

theorem top_serializer_positions (t : (F.atTop colour colour).Labels) :
    (F.atTop colour colour).layers t = tLay word t.1.val ++
      dotsOn word (F.topPositions colour colour t.1 t.2) :=
  F.atTop_layers_dotsOn colour colour t

#print axioms two_position_counts
#print axioms every_top_count_realized
#print axioms top_serializer_positions
end NonVacuity.TopMatchingChoice
