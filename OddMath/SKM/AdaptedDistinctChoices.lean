import OddMath.SKM.AdaptedPointedPair

/-! Complete mutually adapted choices, with literal serializers on both
sides of a target exchange whose selected endpoints are always distinct. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
universe u
variable {I : Type u}

theorem exists_adapted_distinct_choices (a P Q : List (Letter I)) (x y : Letter I)
    (hdist : ∀ T, IsMatching₂ a (P ++ x :: y :: Q) T →
      ¬ Same (pairing₂ a T) (a.length + P.length) (a.length + P.length + 1)) :
    ∃ (F : MatchingBasisChoice a (P ++ x :: y :: Q))
      (G : MatchingBasisChoice a (P ++ y :: x :: Q)) (e : F.Labels ≃ G.Labels),
      ∀ t, G.layers (e t) = F.layers t ++ (xCrL x y).map (xwhL P Q) ∨
        F.layers t = G.layers (e t) ++ (xCrL y x).map (xwhL P Q) := by
  classical
  obtain ⟨B⟩ := MatchingBasisChoice.nonempty a (P ++ x :: y :: Q)
  have hpair (j : B.members) := exists_adapted_pointed_pair a P Q x y
    (B.matching j j.property).1 (hdist j (B.matching j j.property).1)
  choose A hA using hpair
  let L := fun j => (A j).left
  let R := fun j => (A j).right
  have huL : ∀ i j, Iso (pairing₂ a (L i).moves) (pairing₂ a (L j).moves) → i = j := by
    intro i j hij
    apply Subtype.ext
    exact B.unique _ i.property _ j.property ((hA i).symm.trans (hij.trans (hA j)))
  have huR : ∀ i j, Iso (pairing₂ a (R i).moves) (pairing₂ a (R j).moves) → i = j := by
    intro i j hij
    apply huL i j
    have h := (((A i).swapped).symm.trans (hij.trans (A j).swapped)).swapAt (a.length + P.length)
    simpa only [swapAt_swapAt] using h
  have hcL : ∀ T, IsMatching₂ a (P ++ x :: y :: Q) T → StrictReduced₂ a T →
      ∃ j, Iso (pairing₂ a (L j).moves) (pairing₂ a T) := by
    intro T hT ht
    obtain ⟨S, hS, hST⟩ := B.complete T hT ht
    exact ⟨⟨S, hS⟩, (hA ⟨S, hS⟩).trans hST⟩
  have hcR : ∀ T, IsMatching₂ a (P ++ y :: x :: Q) T → StrictReduced₂ a T →
      ∃ j, Iso (pairing₂ a (R j).moves) (pairing₂ a T) := by
    intro T hT _
    obtain ⟨S, hS, hs, hi⟩ := exists_strictReduced_target_swap a P Q y x hT
    obtain ⟨j, hj⟩ := hcL S hS hs
    refine ⟨j, ?_⟩
    have h := (A j).swapped.trans ((hj.trans hi).swapAt (a.length + P.length))
    simpa only [swapAt_swapAt] using h
  let F := IndexedMatchingChoice.choice L huL hcL
  let G := IndexedMatchingChoice.choice R huR hcR
  let eL := IndexedMatchingChoice.labelsEquiv L huL hcL
  let eR := IndexedMatchingChoice.labelsEquiv R huR hcR
  let eM : (Σ j : B.members, MatchingStrand a (L j).moves → ℕ) ≃
      (Σ j : B.members, MatchingStrand a (R j).moves → ℕ) :=
    _root_.Equiv.sigmaCongrRight (fun j => _root_.Equiv.arrowCongr (A j).strands (_root_.Equiv.refl ℕ))
  let e := eL.symm.trans (eM.trans eR)
  refine ⟨F, G, e, ?_⟩
  intro t
  obtain ⟨⟨j, n⟩, rfl⟩ := eL.surjective t
  have he : e (eL ⟨j, n⟩) = eR ⟨j, n ∘ (A j).strands.symm⟩ := by
    simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply, eM, Equiv.sigmaCongrRight_apply]
    rfl
  rw [he, IndexedMatchingChoice.layers_labelsEquiv, IndexedMatchingChoice.layers_labelsEquiv]
  exact (A j).layers n

/-- Different colours cannot be the two endpoints of one strand. -/
theorem target_distinct_colours_not_same {a P Q : List (Letter I)} {x y : Letter I}
    (hxy : x.2 ≠ y.2) {T : List (TMove (Letter I))}
    (hT : IsMatching₂ a (P ++ x :: y :: Q) T) :
    ¬ Same (pairing₂ a T) (a.length + P.length) (a.length + P.length + 1) := by
  intro hs
  have hl := hT.pairing_properties.2.1 _ _ hs (by omega)
  have hletters := hT.pairing_properties.2.2
  have h₀ : ((pairing₂ a T)[a.length + P.length]?).map Prod.snd = some x := by
    rw [← List.getElem?_map, hletters]
    have he : a.length + P.length = (dualW a ++ P).length := by simp [length_dualW]
    rw [he, ← List.append_assoc]
    generalize dualW a ++ P = K
    simp
  have h₁ : ((pairing₂ a T)[a.length + P.length + 1]?).map Prod.snd = some y := by
    rw [← List.getElem?_map, hletters]
    have he : a.length + P.length = (dualW a ++ P).length := by simp [length_dualW]
    rw [he, ← List.append_assoc]
    generalize dualW a ++ P = K
    simp
  have he : some y = (some x).map flipL := by
    rw [← h₁, hl, ← h₀, Option.map_map]
  have hy : y = flipL x := Option.some.inj he
  exact hxy (congrArg Prod.snd hy).symm

/-- Actual complete adapted choices for distinct colours, with no extra
matching-class or serializer hypotheses. -/
theorem exists_adapted_distinct_colour_choices (a P Q : List (Letter I)) (x y : Letter I)
    (hxy : x.2 ≠ y.2) :
    ∃ (F : MatchingBasisChoice a (P ++ x :: y :: Q))
      (G : MatchingBasisChoice a (P ++ y :: x :: Q)) (e : F.Labels ≃ G.Labels),
      ∀ t, G.layers (e t) = F.layers t ++ (xCrL x y).map (xwhL P Q) ∨
        F.layers t = G.layers (e t) ++ (xCrL y x).map (xwhL P Q) :=
  exists_adapted_distinct_choices a P Q x y
    (fun _ h => target_distinct_colours_not_same hxy h)

end OddMath.SKM
