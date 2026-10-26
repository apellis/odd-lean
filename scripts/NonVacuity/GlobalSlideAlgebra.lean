import OddMath.QuiverHecke.CyclotomicAction.GlobalSlideAlgebra
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of the last-pair dot slides: for the odd colour the sign is
`-1`, so the slides read `c y₁ + y₂ c = θ(1)` and `y₁ c + c y₂ = θ(1)` at every height. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
example : heightLastCrossing datum scalars (fun _ => (0 : Polynomial ℚ)) () () 1 *
      heightAppend datum scalars (fun _ => 0) () 2 (heightLastDot datum scalars (fun _ => 0) () 1) +
    heightLastDot datum scalars (fun _ => 0) () 2 *
      heightLastCrossing datum scalars (fun _ => 0) () () 1 =
    heightAppend datum scalars (fun _ => 0) () 2 (heightAppend datum scalars (fun _ => 0) () 1 1) := by
  have h := heightLastCrossing_slide_left datum scalars (fun _ => (0 : Polynomial ℚ)) () 1
  simpa only [show datum.parity () = 1 from rfl, koszulSign_one_one, neg_smul, one_smul,
    sub_neg_eq_add] using h
example : heightAppend datum scalars (fun _ => (0 : Polynomial ℚ)) () 1
      (heightLastDot datum scalars (fun _ => 0) () 0) *
      heightLastCrossing datum scalars (fun _ => 0) () () 0 +
    heightLastCrossing datum scalars (fun _ => 0) () () 0 *
      heightLastDot datum scalars (fun _ => 0) () 1 =
    heightAppend datum scalars (fun _ => 0) () 1 (heightAppend datum scalars (fun _ => 0) () 0 1) := by
  have h := heightLastCrossing_slide_right datum scalars (fun _ => (0 : Polynomial ℚ)) () 0
  simpa only [show datum.parity () = 1 from rfl, koszulSign_one_one, neg_smul, one_smul,
    sub_neg_eq_add] using h
#print axioms OddMath.QuiverHecke.CyclotomicAction.heightLastCrossing_slide_left
#print axioms OddMath.QuiverHecke.CyclotomicAction.heightLastCrossing_slide_right
