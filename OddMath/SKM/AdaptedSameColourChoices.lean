import OddMath.SKM.CupCompletedChoice
import OddMath.SKM.AdaptedPointedPair

/-! Complete same-colour target families. The unpaired sector has literal
terminal crossings; the paired sector has literal cups on common residual
representatives. No independence assumption enters this construction. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
universe u
variable {I : Type u}

/-- Simultaneously complete choices on both sides of a same-colour exchange.
The sum-label equivalences retain every residual label and every cup dot count.
Unpaired low/high correspondence is supplied by `AdaptedPointedPair.layers`. -/
theorem exists_same_colour_adapted_choices (a P Q : List (Letter I)) (ε : Bool) (i : I) :
    ∃ (B : MatchingBasisChoice a (P ++ Q)) (J : Type u)
      (A : J → AdaptedPointedPair a P Q (ε, i) (!ε, i))
      (F : MatchingBasisChoice a (P ++ (ε, i) :: (!ε, i) :: Q))
      (G : MatchingBasisChoice a (P ++ (!ε, i) :: (ε, i) :: Q))
      (eF : ((Σ j : J, MatchingStrand a (A j).left.moves → ℕ) ⊕
        (ℕ × B.Labels)) ≃ F.Labels)
      (eG : ((Σ j : J, MatchingStrand a (A j).right.moves → ℕ) ⊕
        (ℕ × B.Labels)) ≃ G.Labels),
      (∀ j n, F.layers (eF (.inl ⟨j, n⟩)) = (A j).left.layers n) ∧
      (∀ j n, G.layers (eG (.inl ⟨j, n⟩)) = (A j).right.layers n) ∧
      (∀ b (j : B.members) n, F.layers (eF (.inr (b, ⟨j, n⟩))) =
        (PointedMatching.ofStrict (B.matching j j.property).1
          (B.matching j j.property).2).layers n ++
        (xCupL (ε, i)).map (xwhL P Q) ++
        dLay (P ++ (ε, i) :: (!ε, i) :: Q)
          (List.replicate b (.dt (if ε then P.length else P.length + 1)))) ∧
      (∀ b (j : B.members) n, G.layers (eG (.inr (b, ⟨j, n⟩))) =
        (PointedMatching.ofStrict (B.matching j j.property).1
          (B.matching j j.property).2).layers n ++
        (xCupL (!ε, i)).map (xwhL P Q) ++
        dLay (P ++ (!ε, i) :: (ε, i) :: Q)
          (List.replicate b (.dt (if !ε then P.length else P.length + 1)))) := by
  classical
  obtain ⟨C⟩ := MatchingBasisChoice.nonempty a (P ++ (ε, i) :: (!ε, i) :: Q)
  obtain ⟨B⟩ := MatchingBasisChoice.nonempty a (P ++ Q)
  let J := {j : C.members // ¬ Same (pairing₂ a j.val)
    (a.length + P.length) (a.length + P.length + 1)}
  have hex (j : J) := exists_adapted_pointed_pair a P Q (ε, i) (!ε, i)
    (C.matching j.val j.val.property).1 j.property
  choose A hA using hex
  let U := fun j => (A j).left
  let V := fun j => (A j).right
  let R := fun j : B.members => PointedMatching.ofStrict
    (B.matching j j.property).1 (B.matching j j.property).2
  have hu : ∀ j l, Iso (pairing₂ a (U j).moves) (pairing₂ a (U l).moves) → j = l := by
    intro j l h
    apply Subtype.ext
    apply Subtype.ext
    exact C.unique _ j.val.property _ l.val.property ((hA j).symm.trans (h.trans (hA l)))
  have hn : ∀ j, ¬ Same (pairing₂ a (U j).moves)
      (a.length + P.length) (a.length + P.length + 1) :=
    fun j h => j.property (((hA j).2 _ _).mp h)
  have hc : ∀ T, IsMatching₂ a (P ++ (ε, i) :: (!ε, i) :: Q) T →
      StrictReduced₂ a T → ¬ Same (pairing₂ a T)
        (a.length + P.length) (a.length + P.length + 1) →
      ∃ j, Iso (pairing₂ a (U j).moves) (pairing₂ a T) := by
    intro T hT ht hs
    obtain ⟨S, hS, hi⟩ := C.complete T hT ht
    let j : J := ⟨⟨S, hS⟩, fun h => hs ((hi.2 _ _).mp h)⟩
    exact ⟨j, (hA j).trans hi⟩
  have hv : ∀ j l, Iso (pairing₂ a (V j).moves) (pairing₂ a (V l).moves) → j = l := by
    intro j l h
    apply hu j l
    have hh := (((A j).swapped).symm.trans (h.trans (A l).swapped)).swapAt
      (a.length + P.length)
    simpa only [swapAt_swapAt] using hh
  have hvn : ∀ j, ¬ Same (pairing₂ a (V j).moves)
      (a.length + P.length) (a.length + P.length + 1) := by
    intro j h
    have hh := ((A j).swapped.2 _ _).mp h
    rw [same_swapAt (target_pair_bound (U j).matching), tau_left, tau_right] at hh
    exact hn j hh.symm
  have hvc : ∀ T, IsMatching₂ a (P ++ (!ε, i) :: (ε, i) :: Q) T →
      StrictReduced₂ a T → ¬ Same (pairing₂ a T)
        (a.length + P.length) (a.length + P.length + 1) →
      ∃ j, Iso (pairing₂ a (V j).moves) (pairing₂ a T) := by
    intro T hT _ hs
    obtain ⟨S, hS, ht, hi⟩ := exists_strictReduced_target_swap a P Q (!ε, i) (ε, i) hT
    have hnS : ¬ Same (pairing₂ a S) (a.length + P.length) (a.length + P.length + 1) := by
      intro h
      have hh := (hi.2 _ _).mp h
      rw [same_swapAt (target_pair_bound hT), tau_left, tau_right] at hh
      exact hs hh.symm
    obtain ⟨j, hj⟩ := hc S hS ht hnS
    refine ⟨j, ?_⟩
    have hh := (A j).swapped.trans ((hj.trans hi).swapAt (a.length + P.length))
    simpa only [swapAt_swapAt] using hh
  have hr : ∀ j l, Iso (pairing₂ a (R j).moves) (pairing₂ a (R l).moves) → j = l := by
    intro j l h
    apply Subtype.ext
    exact B.unique _ j.property _ l.property h
  have hR : ∀ T, IsMatching₂ a (P ++ Q) T → StrictReduced₂ a T →
      ∃ j, Iso (pairing₂ a (R j).moves) (pairing₂ a T) := by
    intro T hT ht
    obtain ⟨S, hS, hi⟩ := B.complete T hT ht
    exact ⟨⟨S, hS⟩, hi⟩
  obtain ⟨F, eF, hFu, hFp⟩ := exists_cup_completed_choice a P Q ε i U R hu hn hc hr hR
  have HV : ∃ (G : MatchingBasisChoice a (P ++ (!ε, i) :: (ε, i) :: Q))
      (eG : ((Σ j : J, MatchingStrand a (V j).moves → ℕ) ⊕
        (ℕ × B.Labels)) ≃ G.Labels),
      (∀ j n, G.layers (eG (.inl ⟨j, n⟩)) = (V j).layers n) ∧
      (∀ b (j : B.members) n, G.layers (eG (.inr (b, ⟨j, n⟩))) =
        (R j).layers n ++ (xCupL (!ε, i)).map (xwhL P Q) ++
        dLay (P ++ (!ε, i) :: (ε, i) :: Q)
          (List.replicate b (.dt (if !ε then P.length else P.length + 1)))) := by
    cases ε <;> exact exists_cup_completed_choice a P Q _ i V R hv hvn hvc hr hR
  obtain ⟨G, eG, hGu, hGp⟩ := HV
  exact ⟨B, J, A, F, G, eF, eG, hFu, hGu, hFp, hGp⟩

/-- One label equivalence for the two complete families, with the common
paired sector explicitly embedded. Outside that sector the exact terminal
crossing correspondence holds; inside it both cup serializers are specified.
This is the interface used by the same-colour coefficient comparison. -/
theorem exists_same_colour_adapted_equiv (a P Q : List (Letter I)) (ε : Bool) (i : I) :
    ∃ (B : MatchingBasisChoice a (P ++ Q))
      (F : MatchingBasisChoice a (P ++ (ε, i) :: (!ε, i) :: Q))
      (G : MatchingBasisChoice a (P ++ (!ε, i) :: (ε, i) :: Q))
      (e : F.Labels ≃ G.Labels) (p : ℕ × B.Labels ↪ F.Labels),
      (∀ t, t ∉ Set.range p →
        G.layers (e t) = F.layers t ++ (xCrL (ε, i) (!ε, i)).map (xwhL P Q) ∨
        F.layers t = G.layers (e t) ++ (xCrL (!ε, i) (ε, i)).map (xwhL P Q)) ∧
      (∀ b (j : B.members) n,
        let R := PointedMatching.ofStrict (B.matching j j.property).1
          (B.matching j j.property).2
        F.layers (p (b, ⟨j, n⟩)) = R.layers n ++ (xCupL (ε, i)).map (xwhL P Q) ++
          dLay (P ++ (ε, i) :: (!ε, i) :: Q)
            (List.replicate b (.dt (if ε then P.length else P.length + 1))) ∧
        G.layers (e (p (b, ⟨j, n⟩))) = R.layers n ++ (xCupL (!ε, i)).map (xwhL P Q) ++
          dLay (P ++ (!ε, i) :: (ε, i) :: Q)
            (List.replicate b (.dt (if !ε then P.length else P.length + 1)))) := by
  obtain ⟨B, J, A, F, G, eF, eG, hFu, hGu, hFp, hGp⟩ :=
    exists_same_colour_adapted_choices a P Q ε i
  let eu : (Σ j : J, MatchingStrand a (A j).left.moves → ℕ) ≃
      (Σ j : J, MatchingStrand a (A j).right.moves → ℕ) :=
    _root_.Equiv.sigmaCongrRight (fun j =>
      _root_.Equiv.arrowCongr (A j).strands (_root_.Equiv.refl ℕ))
  let E := _root_.Equiv.sumCongr eu (_root_.Equiv.refl (ℕ × B.Labels))
  let e := eF.symm.trans (E.trans eG)
  let p : ℕ × B.Labels ↪ F.Labels :=
    ⟨fun z => eF (.inr z), eF.injective.comp Sum.inr_injective⟩
  have heU (j : J) (n : MatchingStrand a (A j).left.moves → ℕ) :
      e (eF (.inl ⟨j, n⟩)) = eG (.inl ⟨j, n ∘ (A j).strands.symm⟩) := by
    simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply, E,
      Equiv.sumCongr_apply, eu]
    rfl
  have heP (z : ℕ × B.Labels) : e (p z) = eG (.inr z) := by
    simp [e, p, E]
  refine ⟨B, F, G, e, p, ?_, ?_⟩
  · intro t ht
    obtain ⟨z, rfl⟩ := eF.surjective t
    cases z with
    | inl z =>
      obtain ⟨j, n⟩ := z
      rw [heU, hFu, hGu]
      exact (A j).layers n
    | inr z => exact False.elim (ht ⟨z, rfl⟩)
  · intro b j n
    dsimp only
    constructor
    · exact hFp b j n
    · rw [heP]
      exact hGp b j n

end OddMath.SKM
