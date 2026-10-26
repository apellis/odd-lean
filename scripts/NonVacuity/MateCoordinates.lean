import OddMath.SKM.RouquierMateCoordinates

/-!
Signature and axiom audit for the coordinate reduction. The occupied,
noncommutative tests of its two series are in `MateSeries.lean`.
This is not a constructed reservoir–probe categorical action.
-/
open OddMath.SKM
#check @SuperRouquierLoc.MateProjectionFormula.of_coordinates
#print axioms SuperRouquierLoc.MateProjectionFormula.of_coordinates
