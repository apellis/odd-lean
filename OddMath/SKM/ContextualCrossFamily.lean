import OddMath.SKM.ContextualCupFamily
import OddMath.SKM.BoundaryFamily

/-! Literal terminal crossings for the distinct-strand adapted sector. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
variable {I : Type*}

theorem matching_append_cross (a P Q : List (Letter I)) (x y : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (P ++ x :: y :: Q) R) :
    IsMatching₂ a (P ++ y :: x :: Q) (R ++ [.mv (.cross P.length)]) := by
  constructor
  · apply (tFits_snoc _ _ _ _).mpr
    refine ⟨hR.1, ?_⟩
    change a.length + P.length + 1 < (pairing₂ a R).length
    have he := congrArg List.length hR.pairing_properties.2.2
    simp only [List.length_map, List.length_append, List.length_cons, length_dualW] at he
    omega
  · simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, hR.2, tLet, chStep_cross]

@[simp] theorem pairing_append_cross (a P : List (Letter I))
    (R : List (TMove (Letter I))) :
    pairing₂ a (R ++ [.mv (.cross P.length)]) = swapAt (pairing₂ a R) (a.length + P.length) := by
  rw [pairing₂, tRun_snoc']
  rfl

/-- Appending the mutual crossing to two previously noninterleaving distinct
strands preserves strict reducedness and introduces no critical point. -/
theorem strictReduced_append_cross {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a b R) (hr : StrictReduced₂ a R) (p : ℕ)
    (hne : idD (pairing₂ a R) (a.length + p) ≠ idD (pairing₂ a R) (a.length + p + 1))
    (hil : ¬ Ilv2 (pairing₂ a R) (idD (pairing₂ a R) (a.length + p))
      (idD (pairing₂ a R) (a.length + p + 1))) :
    StrictReduced₂ a (R ++ [.mv (.cross p)]) := by
  constructor
  · change CrossOnce (tRun flipL a.length (tStart a) (R ++ [.mv (.cross p)]))
    rw [tRun_snoc']
    exact crossOnce_cross ((tInv_tStart a).run hR.1) hr.1 hne hil
  · change (tCrit flipL a.length (tStart a) [] (R ++ [.mv (.cross p)])).Nodup
    rw [tCrit_snoc]
    exact hr.2

theorem target_pair_bound {a P Q : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (P ++ x :: y :: Q) R) :
    a.length + P.length + 1 < (pairing₂ a R).length := by
  have he := congrArg List.length hR.pairing_properties.2.2
  simp only [List.length_map, List.length_append, List.length_cons, length_dualW] at he
  omega

/-- Realizing the exchanged target pairing works at an arbitrary source. -/
theorem exists_strictReduced_target_swap (a P Q : List (Letter I)) (x y : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (P ++ x :: y :: Q) R) :
    ∃ S, IsMatching₂ a (P ++ y :: x :: Q) S ∧ StrictReduced₂ a S ∧
      Iso (pairing₂ a S) (swapAt (pairing₂ a R) (a.length + P.length)) := by
  obtain ⟨hv, hl, hs⟩ := hR.pairing_properties
  have hp := target_pair_bound hR
  apply exists_strictReduced_matching (hv.swapAt hp)
    (hl.swapAt_of_involutive flipL_involutive hp)
  rw [map_swapAt, hs]
  have he : a.length + P.length = (dualW a ++ P).length := by simp [length_dualW]
  rw [he, ← List.append_assoc, swapAt_mid, List.append_assoc]

/-- The endpoint formulation of the noninterleaving hypothesis directly
controls the actual strict crossing attachment. -/
theorem strictReduced_append_cross_of_not_ilv
    {a P Q : List (Letter I)} {x y : Letter I} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (P ++ x :: y :: Q) R) (hr : StrictReduced₂ a R)
    (hn : ¬ Same (pairing₂ a R) (a.length + P.length) (a.length + P.length + 1))
    (hi : ¬ Ilv (pairing₂ a R) (a.length + P.length)) :
    StrictReduced₂ a (R ++ [.mv (.cross P.length)]) := by
  have hp := target_pair_bound hR
  have h₀ := idAt_eq_idD (show a.length + P.length < (pairing₂ a R).length by omega)
  have h₁ := idAt_eq_idD hp
  apply strictReduced_append_cross hR hr P.length
  · intro he
    apply hn
    exact ⟨by omega, by rw [h₀]; simp, by rw [h₀, h₁, he]⟩
  · exact fun h => hi ((ilv2_iff_ilv hR.pairing_properties.1 h₀ h₁).mp h)

/-- The literal crossing transports strand labels by the endpoint
transposition; it does not choose a colour-only bijection. -/
def terminalCrossStrandEquiv {a P Q : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (P ++ x :: y :: Q) R)
    (hn : ¬ Same (pairing₂ a R) (a.length + P.length) (a.length + P.length + 1)) :
    MatchingStrand a R ≃ MatchingStrand a (R ++ [.mv (.cross P.length)]) :=
  matchingStrandEquivOfSwap (target_pair_bound hR) hn (by
    rw [pairing_append_cross]; exact Iso.refl _)

end OddMath.SKM
