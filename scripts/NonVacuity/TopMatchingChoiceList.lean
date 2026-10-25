import OddMath.SKM.TopMatchingChoiceList
import OddMath.SKM.MatchingChoiceCast

open OddMath.SKM StringDiagrams
noncomputable section
universe u
variable {I : Type u}

example (i j : I) :
    (List.ofFn fun k : Fin ([i] ++ [j]).length =>
      (true, ([i] ++ [j]).get k)) = ups [i] ++ ups [j] :=
  ofFn_up_get_append [i] [j]

example (l a b r : List I)
    (F : MatchingBasisChoice (ups l ++ ups a) (ups b ++ ups r))
    (t : (F.atTopSplit l a b r).Labels) :
    ∃ L : List (LayerData I), SChain (ups l ++ ups a) L (ups b ++ ups r) ∧
      L.map ofL = (F.atTopSplit l a b r).layers t :=
  F.atTopSplit_ordinary l a b r t

#print axioms OddMath.SKM.MatchingBasisChoice.atTopSplit_positiveExpansion_lift
#print axioms OddMath.SKM.MatchingBasisChoice.cast_expansion
