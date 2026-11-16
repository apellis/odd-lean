import OddMath.SKM.IndexedMatchingChoice

/-! Actual pointed low/high partners for the distinct endpoint sector. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
universe u
variable {I : Type u}

structure AdaptedPointedPair (a P Q : List (Letter I)) (x y : Letter I) where
  left : PointedMatching a (P ++ x :: y :: Q)
  right : PointedMatching a (P ++ y :: x :: Q)
  strands : MatchingStrand a left.moves ≃ MatchingStrand a right.moves
  swapped : Iso (pairing₂ a right.moves) (swapAt (pairing₂ a left.moves) (a.length + P.length))
  layers : ∀ n : MatchingStrand a left.moves → ℕ,
    right.layers (n ∘ strands.symm) = left.layers n ++ (xCrL x y).map (xwhL P Q) ∨
    left.layers n = right.layers (n ∘ strands.symm) ++ (xCrL y x).map (xwhL P Q)

 theorem exists_adapted_pointed_pair (a P Q : List (Letter I)) (x y : Letter I)
    {T : List (TMove (Letter I))} (hT : IsMatching₂ a (P ++ x :: y :: Q) T)
    (hn : ¬ Same (pairing₂ a T) (a.length + P.length) (a.length + P.length + 1)) :
    ∃ A : AdaptedPointedPair a P Q x y, Iso (pairing₂ a A.left.moves) (pairing₂ a T) := by
  classical
  by_cases hi : Ilv (pairing₂ a T) (a.length + P.length)
  · obtain ⟨S, hS, hrS, hs⟩ := exists_strictReduced_target_swap a P Q x y hT
    have hp := target_pair_bound hT
    have hnS : ¬ Same (pairing₂ a S) (a.length + P.length) (a.length + P.length + 1) := by
      intro h
      have hh := (hs.2 _ _).mp h
      rw [same_swapAt hp, tau_left, tau_right] at hh
      exact hn hh.symm
    have hiS : ¬ Ilv (pairing₂ a S) (a.length + P.length) := by
      rw [ilv_iff_of_iso hs, ilv_swapAt_iff hT.pairing_properties.1 hp hn]
      exact not_not_intro hi
    let G := PointedMatching.ofStrict hS hrS
    let F := G.appendCross hnS hiS
    let A : AdaptedPointedPair a P Q x y :=
      { left := F
        right := G
        strands := (terminalCrossStrandEquiv G.matching hnS).symm
        swapped := by
          change Iso (pairing₂ a S) (swapAt (pairing₂ a (S ++ [.mv (.cross P.length)])) _)
          rw [pairing_append_cross, swapAt_swapAt]
          exact Iso.refl _
        layers := fun n => Or.inr (G.appendCross_layers_high hnS hiS n) }
    refine ⟨A, ?_⟩
    change Iso (pairing₂ a (S ++ [.mv (.cross P.length)])) (pairing₂ a T)
    rw [pairing_append_cross]
    simpa only [swapAt_swapAt] using hs.swapAt (a.length + P.length)
  · obtain ⟨R, hR, hrR, hr⟩ := exists_strictReduced_matching
      hT.pairing_properties.1 hT.pairing_properties.2.1 hT.pairing_properties.2.2
    have hnR : ¬ Same (pairing₂ a R) (a.length + P.length) (a.length + P.length + 1) :=
      fun h => hn ((hr.2 _ _).mp h)
    have hiR : ¬ Ilv (pairing₂ a R) (a.length + P.length) := by rwa [ilv_iff_of_iso hr]
    let F := PointedMatching.ofStrict hR hrR
    let G := F.appendCross hnR hiR
    let A : AdaptedPointedPair a P Q x y :=
      { left := F
        right := G
        strands := terminalCrossStrandEquiv F.matching hnR
        swapped := by rw [PointedMatching.appendCross_moves, pairing_append_cross]; exact Iso.refl _
        layers := fun n => Or.inl (F.appendCross_layers hnR hiR n) }
    exact ⟨A, hr⟩

end OddMath.SKM
