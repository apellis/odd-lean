import OddMath.SKM.AdaptedDistinctChoices

open OddMath.SKM StringDiagrams
noncomputable section

/-- Two genuinely different colours, arbitrary through and boundary contexts,
and every strand-dot multiplicity in the actual complete families. -/
example (a P Q : List (Letter Bool)) :
    ∃ (F : MatchingBasisChoice a (P ++ (true, true) :: (false, false) :: Q))
      (G : MatchingBasisChoice a (P ++ (false, false) :: (true, true) :: Q))
      (e : F.Labels ≃ G.Labels),
      ∀ t, G.layers (e t) = F.layers t ++ (xCrL (true, true) (false, false)).map (xwhL P Q) ∨
        F.layers t = G.layers (e t) ++ (xCrL (false, false) (true, true)).map (xwhL P Q) :=
  exists_adapted_distinct_colour_choices a P Q (true, true) (false, false) (by decide)

#print axioms OddMath.SKM.exists_adapted_distinct_colour_choices
#print axioms OddMath.SKM.IndexedMatchingChoice.layers_labelsEquiv
#print axioms OddMath.SKM.PointedMatching.appendCross_layers
