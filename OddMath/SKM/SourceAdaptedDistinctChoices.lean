import OddMath.SKM.SourceCrossAttachment

/-! Complete mutually adapted choices, with literal serializers on both
sides of a source exchange whose selected endpoints are always distinct. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open SourceCrossAttachment
universe u
variable {I : Type u}

theorem exists_source_adapted_distinct_choices (Z P Q : List (Letter I)) (x y : Letter I)
    (hdist : ∀ T, IsMatching₂ (P ++ x :: y :: Q) Z T →
      ¬ Same (pairing₂ (P ++ x :: y :: Q) T) Q.length (Q.length + 1)) :
    ∃ (F : MatchingBasisChoice (P ++ x :: y :: Q) Z)
      (G : MatchingBasisChoice (P ++ y :: x :: Q) Z) (e : F.Labels ≃ G.Labels),
      ∀ t, G.layers (e t) = (xCrL y x).map (xwhL P Q) ++ F.layers t ∨
        F.layers t = (xCrL x y).map (xwhL P Q) ++ G.layers (e t) := by
  classical
  obtain ⟨B⟩ := MatchingBasisChoice.nonempty (P ++ x :: y :: Q) Z
  have hpair (j : B.members) := SourceCrossAttachment.exists_adapted_pointed_pair P Q Z x y
    (B.matching j j.property).1 (hdist j (B.matching j j.property).1)
  choose A hA using hpair
  let L := fun j => (A j).left
  let R := fun j => (A j).right
  have huL : ∀ i j, Iso (pairing₂ (P ++ x :: y :: Q) (L i).moves) (pairing₂ (P ++ x :: y :: Q) (L j).moves) → i = j := by
    intro i j hij
    apply Subtype.ext
    exact B.unique _ i.property _ j.property ((hA i).symm.trans (hij.trans (hA j)))
  have huR : ∀ i j, Iso (pairing₂ (P ++ y :: x :: Q) (R i).moves) (pairing₂ (P ++ y :: x :: Q) (R j).moves) → i = j := by
    intro i j hij
    apply huL i j
    have h := (((A i).swapped).symm.trans (hij.trans (A j).swapped)).swapAt Q.length
    simpa only [swapAt_swapAt] using h
  have hcL : ∀ T, IsMatching₂ (P ++ x :: y :: Q) Z T → StrictReduced₂ (P ++ x :: y :: Q) T →
      ∃ j, Iso (pairing₂ (P ++ x :: y :: Q) (L j).moves) (pairing₂ (P ++ x :: y :: Q) T) := by
    intro T hT ht
    obtain ⟨S, hS, hST⟩ := B.complete T hT ht
    exact ⟨⟨S, hS⟩, (hA ⟨S, hS⟩).trans hST⟩
  have hcR : ∀ T, IsMatching₂ (P ++ y :: x :: Q) Z T → StrictReduced₂ (P ++ y :: x :: Q) T →
      ∃ j, Iso (pairing₂ (P ++ y :: x :: Q) (R j).moves) (pairing₂ (P ++ y :: x :: Q) T) := by
    intro T hT _
    obtain ⟨S, hS, hs, hi⟩ := exists_strictReduced_source_swap P Q Z y x hT
    obtain ⟨j, hj⟩ := hcL S hS hs
    refine ⟨j, ?_⟩
    have h := (A j).swapped.trans ((hj.trans hi).swapAt Q.length)
    simpa only [swapAt_swapAt] using h
  let F := IndexedMatchingChoice.choice L huL hcL
  let G := IndexedMatchingChoice.choice R huR hcR
  let eL := IndexedMatchingChoice.labelsEquiv L huL hcL
  let eR := IndexedMatchingChoice.labelsEquiv R huR hcR
  let eM : (Σ j : B.members, MatchingStrand (P ++ x :: y :: Q) (L j).moves → ℕ) ≃
      (Σ j : B.members, MatchingStrand (P ++ y :: x :: Q) (R j).moves → ℕ) :=
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
theorem source_distinct_colours_not_same {Z P Q : List (Letter I)} {x y : Letter I}
    (hxy : x.2 ≠ y.2) {T : List (TMove (Letter I))}
    (hT : IsMatching₂ (P ++ x :: y :: Q) Z T) :
    ¬ Same (pairing₂ (P ++ x :: y :: Q) T) Q.length (Q.length + 1) := by
  intro hs
  have hl := hT.pairing_properties.2.1 _ _ hs (by omega)
  have hletters := hT.pairing_properties.2.2
  have h₀ : ((pairing₂ (P ++ x :: y :: Q) T)[Q.length]?).map Prod.snd = some (flipL y) := by
    rw [← List.getElem?_map, hletters]
    simp only [dualW_append, dualW_cons, List.append_assoc, List.cons_append,
      List.nil_append]
    rw [← length_dualW Q]
    simp
  have h₁ : ((pairing₂ (P ++ x :: y :: Q) T)[Q.length + 1]?).map Prod.snd = some (flipL x) := by
    rw [← List.getElem?_map, hletters]
    simp only [dualW_append, dualW_cons, List.append_assoc, List.cons_append,
      List.nil_append]
    rw [← length_dualW Q]
    simp
  have he : some (flipL x) = (some (flipL y)).map flipL := by
    rw [← h₁, hl, ← h₀, Option.map_map]
  have hy : flipL x = flipL (flipL y) := Option.some.inj he
  apply hxy
  simpa only [flipL] using congrArg Prod.snd hy

/-- Actual complete adapted choices for distinct colours, with no extra
matching-class or serializer hypotheses. -/
theorem exists_source_adapted_distinct_colour_choices (Z P Q : List (Letter I)) (x y : Letter I)
    (hxy : x.2 ≠ y.2) :
    ∃ (F : MatchingBasisChoice (P ++ x :: y :: Q) Z)
      (G : MatchingBasisChoice (P ++ y :: x :: Q) Z) (e : F.Labels ≃ G.Labels),
      ∀ t, G.layers (e t) = (xCrL y x).map (xwhL P Q) ++ F.layers t ∨
        F.layers t = (xCrL x y).map (xwhL P Q) ++ G.layers (e t) :=
  exists_source_adapted_distinct_choices Z P Q x y
    (fun _ h => source_distinct_colours_not_same hxy h)

end OddMath.SKM
