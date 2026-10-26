import OddMath.QuiverHecke.CyclotomicAction.GlobalHeight
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! The all-height extension retains the nonzero odd rank-one vacuum inclusion. -/
noncomputable section
open CategoryTheory StringDiagrams
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples

private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h

example : heightAppend datum scalars (fun _ => 0) () 0 1 ≠ 0 :=
  VacuumExamples.vacuum_unit_ne_zero

example : Supercategory ℚ (GlobalContentModules datum scalars (fun _ => 0) hp 0) := inferInstance

example : HeightModules datum scalars (fun _ => 0) hp 1 =
    CyclotomicSupermodules datum scalars (fun _ => 0) hp 0 :=
  heightModules_succ datum scalars (fun _ => 0) hp 0

#print axioms OddMath.QuiverHecke.CyclotomicAction.heightAppend_parity
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalContentModules_zero
