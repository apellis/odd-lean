import OddMath.SKM.ContextualBoundaryInduction

namespace NonVacuity.ContextualBoundaryInduction
open OddMath.SKM OddMath.SKM.ContextualBoundary

/-- Alternating orientations with distinct and repeated colors genuinely
require more than one adjacent sorting step. -/
theorem alternating_inversions :
    inversions true ([dn false, up true, dn true, up false] : List (Letter Bool)) = 3 ∧
    inversions false ([up true, dn false, up false, dn true] : List (Letter Bool)) = 3 := by
  decide

theorem contextual_swap :
    inversions true ([dn true] ++ dn false :: up true :: [up false]) =
      inversions true ([dn true] ++ up true :: dn false :: [up false]) + 1 :=
  inversions_swap true [dn true] [up false] false true

/-- A concrete finite derivation tree records both exchange and shorter-pair
branches. This witness concerns boundary reduction, not evaluation independence. -/
inductive Tree : List (Letter Bool) → List (Letter Bool) → Prop
  | sorted (u d e v : List Bool) : Tree (signed true u ++ signed false d) (signed false e ++ signed true v)
  | source (L Q : List (Letter Bool)) (i j : Bool) (b : List (Letter Bool)) :
      Tree (L ++ up j :: dn i :: Q) b → (i = j → Tree (L ++ Q) b) →
      Tree (L ++ dn i :: up j :: Q) b
  | target (a L Q : List (Letter Bool)) (i j : Bool) :
      Tree a (L ++ dn j :: up i :: Q) → (i = j → Tree a (L ++ Q)) →
      Tree a (L ++ up i :: dn j :: Q)

theorem alternating_tree :
    Tree [dn false, up true, dn true, up false] [up true, dn false, up false, dn true] :=
  boundary_induction Tree Tree.sorted Tree.source Tree.target _ _

#print axioms boundary_induction
#print axioms alternating_tree
end NonVacuity.ContextualBoundaryInduction
