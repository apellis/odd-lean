import OddMath.SKM.PointedCupMatching
import OddMath.SKM.IndexedMatchingChoice

/-! Complete target families obtained by joining unpaired representatives to
literal contextual cups on a complete shortened-boundary family. This is the
same-colour family construction needed by contextual nondegeneracy descent. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
universe u v w
variable {I : Type u} {J : Type v} {K : Type w}

/-- Complete unpaired representatives and complete residual representatives
combine into a genuine matching choice. The displayed equivalence accounts for
all labels, and both serializer equations are literal equalities of layers. -/
theorem exists_cup_completed_choice (a P Q : List (Letter I)) (ε : Bool) (i : I)
    (U : J → PointedMatching a (P ++ (ε, i) :: (!ε, i) :: Q))
    (R : K → PointedMatching a (P ++ Q))
    (hu : ∀ j l, Iso (pairing₂ a (U j).moves) (pairing₂ a (U l).moves) → j = l)
    (hn : ∀ j, ¬ Same (pairing₂ a (U j).moves)
      (a.length + P.length) (a.length + P.length + 1))
    (hc : ∀ T, IsMatching₂ a (P ++ (ε, i) :: (!ε, i) :: Q) T →
      StrictReduced₂ a T →
      ¬ Same (pairing₂ a T) (a.length + P.length) (a.length + P.length + 1) →
      ∃ j, Iso (pairing₂ a (U j).moves) (pairing₂ a T))
    (hr : ∀ j l, Iso (pairing₂ a (R j).moves) (pairing₂ a (R l).moves) → j = l)
    (hR : ∀ T, IsMatching₂ a (P ++ Q) T → StrictReduced₂ a T →
      ∃ j, Iso (pairing₂ a (R j).moves) (pairing₂ a T)) :
    ∃ (F : MatchingBasisChoice a (P ++ (ε, i) :: (!ε, i) :: Q))
      (e : ((Σ j : J, MatchingStrand a (U j).moves → ℕ) ⊕
        (ℕ × (Σ j : K, MatchingStrand a (R j).moves → ℕ))) ≃ F.Labels),
      (∀ j n, F.layers (e (.inl ⟨j, n⟩)) = (U j).layers n) ∧
      (∀ b j n, F.layers (e (.inr (b, ⟨j, n⟩))) =
        (R j).layers n ++ (xCupL (ε, i)).map (xwhL P Q) ++
          dLay (P ++ (ε, i) :: (!ε, i) :: Q)
            (List.replicate b (.dt (if ε then P.length else P.length + 1)))) := by
  classical
  let V : J ⊕ K → PointedMatching a (P ++ (ε, i) :: (!ε, i) :: Q) :=
    Sum.elim U (fun j => (R j).appendCup ε i)
  have hp (j : K) : Same (pairing₂ a (V (.inr j)).moves)
      (a.length + P.length) (a.length + P.length + 1) := by
    change Same (pairing₂ a ((R j).moves ++ [.mv (.cup P.length (ε, i))])) _ _
    rw [pairing_append_cup]
    exact (cup_inserted_properties a P Q ε i (R j).matching).2.2.2.1
  have hv : ∀ j l, Iso (pairing₂ a (V j).moves) (pairing₂ a (V l).moves) → j = l := by
    intro j l h
    cases j with
    | inl j =>
      cases l with
      | inl l => exact congrArg Sum.inl (hu j l h)
      | inr l => exact False.elim (hn j ((h.2 _ _).mpr (hp l)))
    | inr j =>
      cases l with
      | inl l => exact False.elim (hn l ((h.2 _ _).mp (hp j)))
      | inr l =>
        apply congrArg Sum.inr
        apply hr j l
        have hd := h.rmAt (hp j).lt_right
        change Iso (rmAt (pairing₂ a ((R j).moves ++ [.mv (.cup P.length (ε, i))])) _)
          (rmAt (pairing₂ a ((R l).moves ++ [.mv (.cup P.length (ε, i))])) _) at hd
        rw [pairing_append_cup, pairing_append_cup,
          (cup_inserted_properties a P Q ε i (R j).matching).2.2.2.2,
          (cup_inserted_properties a P Q ε i (R l).matching).2.2.2.2] at hd
        exact hd
  have hvC : ∀ T, IsMatching₂ a (P ++ (ε, i) :: (!ε, i) :: Q) T →
      StrictReduced₂ a T → ∃ j, Iso (pairing₂ a (V j).moves) (pairing₂ a T) := by
    intro T hT ht
    by_cases hs : Same (pairing₂ a T) (a.length + P.length) (a.length + P.length + 1)
    · obtain ⟨S, hS, hsS, hST⟩ := exists_strictReduced_cup_delete a P Q ε i hT hs
      obtain ⟨j, hj⟩ := hR S hS hsS
      refine ⟨.inr j, ?_⟩
      change Iso (pairing₂ a ((R j).moves ++ [.mv (.cup P.length (ε, i))])) _
      rw [pairing_append_cup]
      have hI := cup_inserted_properties a P Q ε i (R j).matching
      apply cap_iso_of_deleted hI.1 hT.pairing_properties.1 hI.2.2.2.1 hs
        (hI.2.2.1.trans hT.pairing_properties.2.2.symm)
      rw [hI.2.2.2.2]
      exact hj.trans hST
    · obtain ⟨j, hj⟩ := hc T hT ht hs
      exact ⟨.inl j, hj⟩
  let F := IndexedMatchingChoice.choice V hv hvC
  let E := IndexedMatchingChoice.labelsEquiv V hv hvC
  let e₀ : ((Σ j : J, MatchingStrand a (U j).moves → ℕ) ⊕
      (ℕ × (Σ j : K, MatchingStrand a (R j).moves → ℕ))) ≃
      (Σ j : J ⊕ K, MatchingStrand a (V j).moves → ℕ) :=
    { toFun := fun z => match z with
        | .inl ⟨j, n⟩ => ⟨.inl j, n⟩
        | .inr (b, ⟨j, n⟩) => ⟨.inr j, (terminalCupCountsEquiv (R j).matching ε i).symm (b, n)⟩
      invFun := fun z => match z with
        | ⟨.inl j, n⟩ => .inl ⟨j, n⟩
        | ⟨.inr j, n⟩ =>
          let c := terminalCupCountsEquiv (R j).matching ε i n
          .inr (c.1, ⟨j, c.2⟩)
      left_inv := by
        rintro (⟨j, n⟩ | ⟨b, j, n⟩)
        · rfl
        · simp only [Equiv.apply_symm_apply]
      right_inv := by
        rintro ⟨j | j, n⟩
        · rfl
        · simp only [Prod.mk.eta, Equiv.symm_apply_apply] }
  refine ⟨F, e₀.trans E, ?_, ?_⟩
  · intro j n
    exact IndexedMatchingChoice.layers_labelsEquiv V hv hvC (.inl j) n
  · intro b j n
    change F.layers (E ⟨.inr j, (terminalCupCountsEquiv (R j).matching ε i).symm (b, n)⟩) = _
    rw [IndexedMatchingChoice.layers_labelsEquiv]
    exact (R j).appendCup_layers ε i b n

end OddMath.SKM
