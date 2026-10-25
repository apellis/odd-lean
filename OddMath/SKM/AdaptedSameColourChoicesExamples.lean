import OddMath.SKM.AdaptedSameColourChoices

/-! Same-colour adapted families in both orientations and nonempty contexts. -/
noncomputable section
namespace OddMath.SKM.AdaptedSameColourChoicesExamples
open StringDiagrams

private abbrev P : List (Letter Bool) := [up false]
private abbrev Q : List (Letter Bool) := [dn true]
private abbrev a : List (Letter Bool) := P ++ Q

/-- Both sectors of complete same-colour choices occur in the interface;
there is no independence, scalar, grading, or action assumption. -/
theorem complete_exchange (ε : Bool) :
    ∃ (B : MatchingBasisChoice a (P ++ Q))
      (F : MatchingBasisChoice a (P ++ (ε, false) :: (!ε, false) :: Q))
      (G : MatchingBasisChoice a (P ++ (!ε, false) :: (ε, false) :: Q))
      (e : F.Labels ≃ G.Labels) (p : ℕ × B.Labels ↪ F.Labels),
      (∀ t, t ∉ Set.range p →
        G.layers (e t) = F.layers t ++ (xCrL (ε, false) (!ε, false)).map (xwhL P Q) ∨
        F.layers t = G.layers (e t) ++ (xCrL (!ε, false) (ε, false)).map (xwhL P Q)) ∧
      (∀ b (j : B.members) n,
        let R := PointedMatching.ofStrict (B.matching j j.property).1
          (B.matching j j.property).2
        F.layers (p (b, ⟨j, n⟩)) = R.layers n ++ (xCupL (ε, false)).map (xwhL P Q) ++
          dLay (P ++ (ε, false) :: (!ε, false) :: Q)
            (List.replicate b (.dt (if ε then P.length else P.length + 1))) ∧
        G.layers (e (p (b, ⟨j, n⟩))) = R.layers n ++ (xCupL (!ε, false)).map (xwhL P Q) ++
          dLay (P ++ (!ε, false) :: (ε, false) :: Q)
            (List.replicate b (.dt (if !ε then P.length else P.length + 1)))) :=
  exists_same_colour_adapted_equiv a P Q ε false

#print axioms exists_same_colour_adapted_choices
#print axioms exists_same_colour_adapted_equiv
#print axioms complete_exchange
end OddMath.SKM.AdaptedSameColourChoicesExamples
