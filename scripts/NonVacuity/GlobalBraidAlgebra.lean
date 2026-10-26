import OddMath.QuiverHecke.CyclotomicAction.GlobalBraidAlgebra
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of the equal-colour braid on three appended odd strands, at
height three and in the affine algebra on the empty word. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
example : datum.parity () = 1 := rfl
example :
    heightAppend datum scalars (fun _ => (0 : Polynomial ℚ)) () 2
        (heightLastCrossing datum scalars (fun _ => 0) () () 0) *
      (heightLastCrossing datum scalars (fun _ => 0) () () 1 *
        heightAppend datum scalars (fun _ => 0) () 2
          (heightLastCrossing datum scalars (fun _ => 0) () () 0)) =
    heightLastCrossing datum scalars (fun _ => 0) () () 1 *
      (heightAppend datum scalars (fun _ => 0) () 2
          (heightLastCrossing datum scalars (fun _ => 0) () () 0) *
        heightLastCrossing datum scalars (fun _ => 0) () () 1) :=
  heightLastCrossing_braid_same datum scalars (fun _ => 0) () 0
example (w : Word Unit 0) :
    appendHom datum scalars () _ _ (inductionLastCrossing datum scalars () () w) ≫
        inductionLastCrossing datum scalars () () (appendWord () w) ≫
          appendHom datum scalars () _ _ (inductionLastCrossing datum scalars () () w) =
      inductionLastCrossing datum scalars () () (appendWord () w) ≫
        appendHom datum scalars () _ _ (inductionLastCrossing datum scalars () () w) ≫
          inductionLastCrossing datum scalars () () (appendWord () w) :=
  induction_braid_same datum scalars () w
#print axioms OddMath.QuiverHecke.CyclotomicAction.heightLastCrossing_braid_same
