import OddMath.SKM.SourceCapAttachment
import OddMath.SKM.IndexedMatchingChoice

/-! Complete source families for contextual nondegeneracy descent: the paired
sector is an initial dotted cap on a prescribed complete residual family. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open SourceCapAttachment
universe u v w
variable {I : Type u} {J : Type v} {K : Type w}

/-- Join complete unpaired and residual families, retaining every cap exponent
and residual strand count and the literal initial-cap serializer. -/
theorem exists_source_completed_choice (L Q Z : List (Letter I)) (x : Letter I)
    (U : J → PointedMatching (L ++ flipL x :: x :: Q) Z)
    (R : K → PointedMatching (L ++ Q) Z)
    (hu : ∀ j l, Iso (pairing₂ (L ++ flipL x :: x :: Q) (U j).moves)
      (pairing₂ (L ++ flipL x :: x :: Q) (U l).moves) → j = l)
    (hn : ∀ j, ¬ Same (pairing₂ (L ++ flipL x :: x :: Q) (U j).moves)
      Q.length (Q.length + 1))
    (hc : ∀ T, IsMatching₂ (L ++ flipL x :: x :: Q) Z T →
      StrictReduced₂ (L ++ flipL x :: x :: Q) T →
      ¬ Same (pairing₂ (L ++ flipL x :: x :: Q) T) Q.length (Q.length + 1) →
      ∃ j, Iso (pairing₂ (L ++ flipL x :: x :: Q) (U j).moves)
        (pairing₂ (L ++ flipL x :: x :: Q) T))
    (hr : ∀ j l, Iso (pairing₂ (L ++ Q) (R j).moves)
      (pairing₂ (L ++ Q) (R l).moves) → j = l)
    (hR : ∀ T, IsMatching₂ (L ++ Q) Z T → StrictReduced₂ (L ++ Q) T →
      ∃ j, Iso (pairing₂ (L ++ Q) (R j).moves) (pairing₂ (L ++ Q) T)) :
    ∃ (F : MatchingBasisChoice (L ++ flipL x :: x :: Q) Z)
      (e : ((Σ j : J, MatchingStrand (L ++ flipL x :: x :: Q) (U j).moves → ℕ) ⊕
        (ℕ × (Σ j : K, MatchingStrand (L ++ Q) (R j).moves → ℕ))) ≃ F.Labels),
      (∀ j n, F.layers (e (.inl ⟨j, n⟩)) = (U j).layers n) ∧
      (∀ b j n, F.layers (e (.inr (b, ⟨j, n⟩))) =
        (List.replicate b (dotOn (L ++ flipL x :: x :: Q) L.length)).flatten ++
          (xCapL x).map (xwhL L Q) ++ (R j).layers n) := by
  classical
  let V : J ⊕ K → PointedMatching (L ++ flipL x :: x :: Q) Z :=
    Sum.elim U (fun j => attach x (R j))
  have hp (j : K) : Same (pairing₂ (L ++ flipL x :: x :: Q) (V (.inr j)).moves)
      Q.length (Q.length + 1) := cap_same L Q x (R j).moves (R j).matching.1
  have hv : ∀ j l, Iso (pairing₂ (L ++ flipL x :: x :: Q) (V j).moves)
      (pairing₂ (L ++ flipL x :: x :: Q) (V l).moves) → j = l := by
    intro j l h
    cases j with
    | inl j =>
      cases l with
      | inl l => exact congrArg Sum.inl (hu j l h)
      | inr l => exact False.elim (hn j ((h.2 _ _).mpr (hp l)))
    | inr j =>
      cases l with
      | inl l => exact False.elim (hn l ((h.2 _ _).mp (hp j)))
      | inr l => exact congrArg Sum.inr (hr j l
          ((cap_pairing_iso_iff x (R j).matching (R l).matching).mp h))
  have hvC : ∀ T, IsMatching₂ (L ++ flipL x :: x :: Q) Z T →
      StrictReduced₂ (L ++ flipL x :: x :: Q) T →
      ∃ j, Iso (pairing₂ (L ++ flipL x :: x :: Q) (V j).moves)
        (pairing₂ (L ++ flipL x :: x :: Q) T) := by
    intro T hT ht
    by_cases hs : Same (pairing₂ (L ++ flipL x :: x :: Q) T) Q.length (Q.length + 1)
    · obtain ⟨S, hS, hsS, _, _, hST⟩ := exists_cap_adapted x hT hs
      obtain ⟨j, hj⟩ := hR S hS hsS
      exact ⟨.inr j, ((cap_pairing_iso_iff x (R j).matching hS).mpr hj).trans hST⟩
    · obtain ⟨j, hj⟩ := hc T hT ht hs
      exact ⟨.inl j, hj⟩
  let F := IndexedMatchingChoice.choice V hv hvC
  let E := IndexedMatchingChoice.labelsEquiv V hv hvC
  let e₀ : ((Σ j : J, MatchingStrand (L ++ flipL x :: x :: Q) (U j).moves → ℕ) ⊕
      (ℕ × (Σ j : K, MatchingStrand (L ++ Q) (R j).moves → ℕ))) ≃
      (Σ j : J ⊕ K, MatchingStrand (L ++ flipL x :: x :: Q) (V j).moves → ℕ) :=
    { toFun := fun z => match z with
        | .inl ⟨j, n⟩ => ⟨.inl j, n⟩
        | .inr (b, ⟨j, n⟩) => ⟨.inr j, (labelEquiv x (R j).matching).symm (b, n)⟩
      invFun := fun z => match z with
        | ⟨.inl j, n⟩ => .inl ⟨j, n⟩
        | ⟨.inr j, n⟩ =>
          let c := labelEquiv x (R j).matching n
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
    change F.layers (E ⟨.inr j, (labelEquiv x (R j).matching).symm (b, n)⟩) = _
    rw [IndexedMatchingChoice.layers_labelsEquiv]
    change (attach x (R j)).layers _ = _
    rw [attach_layers, Equiv.apply_symm_apply]

/-- Opposite orientation of the cap completion, normalized before constructing families. -/
theorem exists_source_completed_choice_opposite (L Q Z : List (Letter I)) (ε : Bool) (i : I)
    (U : J → PointedMatching (L ++ (ε, i) :: (!ε, i) :: Q) Z)
    (R : K → PointedMatching (L ++ Q) Z)
    (hu : ∀ j l, Iso (pairing₂ (L ++ (ε, i) :: (!ε, i) :: Q) (U j).moves)
      (pairing₂ (L ++ (ε, i) :: (!ε, i) :: Q) (U l).moves) → j = l)
    (hn : ∀ j, ¬ Same (pairing₂ (L ++ (ε, i) :: (!ε, i) :: Q) (U j).moves)
      Q.length (Q.length + 1))
    (hc : ∀ T, IsMatching₂ (L ++ (ε, i) :: (!ε, i) :: Q) Z T →
      StrictReduced₂ (L ++ (ε, i) :: (!ε, i) :: Q) T →
      ¬ Same (pairing₂ (L ++ (ε, i) :: (!ε, i) :: Q) T) Q.length (Q.length + 1) →
      ∃ j, Iso (pairing₂ (L ++ (ε, i) :: (!ε, i) :: Q) (U j).moves)
        (pairing₂ (L ++ (ε, i) :: (!ε, i) :: Q) T))
    (hr : ∀ j l, Iso (pairing₂ (L ++ Q) (R j).moves)
      (pairing₂ (L ++ Q) (R l).moves) → j = l)
    (hR : ∀ T, IsMatching₂ (L ++ Q) Z T → StrictReduced₂ (L ++ Q) T →
      ∃ j, Iso (pairing₂ (L ++ Q) (R j).moves) (pairing₂ (L ++ Q) T)) :
    ∃ (F : MatchingBasisChoice (L ++ (ε, i) :: (!ε, i) :: Q) Z)
      (e : ((Σ j : J, MatchingStrand (L ++ (ε, i) :: (!ε, i) :: Q) (U j).moves → ℕ) ⊕
        (ℕ × (Σ j : K, MatchingStrand (L ++ Q) (R j).moves → ℕ))) ≃ F.Labels),
      (∀ j n, F.layers (e (.inl ⟨j, n⟩)) = (U j).layers n) ∧
      (∀ b j n, F.layers (e (.inr (b, ⟨j, n⟩))) =
        (List.replicate b (dotOn (L ++ (ε, i) :: (!ε, i) :: Q) L.length)).flatten ++
          (xCapL (!ε, i)).map (xwhL L Q) ++ (R j).layers n) := by
  cases ε with
  | false => exact exists_source_completed_choice L Q Z (true, i) U R hu hn hc hr hR
  | true => exact exists_source_completed_choice L Q Z (false, i) U R hu hn hc hr hR

end OddMath.SKM
