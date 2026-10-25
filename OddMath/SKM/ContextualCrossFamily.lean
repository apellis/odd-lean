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

/-- Every distinct-strand class has a pair of strict representatives on the
two exchanged targets, related by one literal terminal crossing on the
noninterleaving side. The original class is retained exactly up to pairing Iso. -/
theorem exists_adapted_distinct_pair (a P Q : List (Letter I)) (x y : Letter I)
    {T : List (TMove (Letter I))} (hT : IsMatching₂ a (P ++ x :: y :: Q) T)
    (hn : ¬ Same (pairing₂ a T) (a.length + P.length) (a.length + P.length + 1)) :
    ∃ R S, IsMatching₂ a (P ++ x :: y :: Q) R ∧ StrictReduced₂ a R ∧
      IsMatching₂ a (P ++ y :: x :: Q) S ∧ StrictReduced₂ a S ∧
      Iso (pairing₂ a R) (pairing₂ a T) ∧
      Iso (pairing₂ a S) (swapAt (pairing₂ a R) (a.length + P.length)) ∧
      (S = R ++ [.mv (.cross P.length)] ∨ R = S ++ [.mv (.cross P.length)]) := by
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
    let R := S ++ [.mv (.cross P.length)]
    refine ⟨R, S, matching_append_cross a P Q y x hS,
      strictReduced_append_cross_of_not_ilv hS hrS hnS hiS, hS, hrS, ?_, ?_, Or.inr rfl⟩
    · rw [show pairing₂ a R = swapAt (pairing₂ a S) (a.length + P.length) from
        pairing_append_cross a P S]
      simpa only [swapAt_swapAt] using hs.swapAt (a.length + P.length)
    · rw [show pairing₂ a R = swapAt (pairing₂ a S) (a.length + P.length) from
        pairing_append_cross a P S, swapAt_swapAt]
      exact Iso.refl _
  · obtain ⟨R, hR, hrR, hr⟩ := exists_strictReduced_matching
      hT.pairing_properties.1 hT.pairing_properties.2.1 hT.pairing_properties.2.2
    have hnR : ¬ Same (pairing₂ a R) (a.length + P.length) (a.length + P.length + 1) :=
      fun h => hn ((hr.2 _ _).mp h)
    have hiR : ¬ Ilv (pairing₂ a R) (a.length + P.length) := by
      rwa [ilv_iff_of_iso hr]
    refine ⟨R, R ++ [.mv (.cross P.length)], hR, hrR,
      matching_append_cross a P Q x y hR,
      strictReduced_append_cross_of_not_ilv hR hrR hnR hiR, hr, ?_, Or.inl rfl⟩
    rw [pairing_append_cross]
    exact Iso.refl _

/-- The literal crossing transports strand labels by the endpoint
transposition; it does not choose a colour-only bijection. -/
def terminalCrossStrandEquiv {a P Q : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (P ++ x :: y :: Q) R)
    (hn : ¬ Same (pairing₂ a R) (a.length + P.length) (a.length + P.length + 1)) :
    MatchingStrand a R ≃ MatchingStrand a (R ++ [.mv (.cross P.length)]) :=
  matchingStrandEquivOfSwap (target_pair_bound hR) hn (by
    rw [pairing_append_cross]; exact Iso.refl _)

@[simp] theorem terminalCrossStrandEquiv_val {a P Q : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (P ++ x :: y :: Q) R)
    (hn : ¬ Same (pairing₂ a R) (a.length + P.length) (a.length + P.length + 1))
    (j : MatchingStrand a R) :
    (terminalCrossStrandEquiv hR hn j).val = tau (a.length + P.length) j.val := rfl

def terminalCrossCountsEquiv {a P Q : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (P ++ x :: y :: Q) R)
    (hn : ¬ Same (pairing₂ a R) (a.length + P.length) (a.length + P.length + 1)) :
    (MatchingStrand a R → ℕ) ≃ (MatchingStrand a (R ++ [.mv (.cross P.length)]) → ℕ) :=
  _root_.Equiv.arrowCongr (terminalCrossStrandEquiv hR hn) (_root_.Equiv.refl ℕ)

@[simp] theorem terminalCrossCountsEquiv_apply {a P Q : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (P ++ x :: y :: Q) R)
    (hn : ¬ Same (pairing₂ a R) (a.length + P.length) (a.length + P.length + 1))
    (n : MatchingStrand a R → ℕ) (j : MatchingStrand a R) :
    terminalCrossCountsEquiv hR hn n (terminalCrossStrandEquiv hR hn j) = n j := by
  simp [terminalCrossCountsEquiv]

end OddMath.SKM
