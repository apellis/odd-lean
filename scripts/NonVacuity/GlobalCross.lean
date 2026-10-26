import OddMath.QuiverHecke.CyclotomicAction.GlobalCross
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization with a nonzero cyclotomic vacuum image. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
example : (globalBlockCross datum scalars (fun _ => 0) hp () () 0 {()} ({()} + ({()} + {()})) rfl).IsHomogeneous 1 :=
  globalBlockCross_homogeneous datum scalars (fun _ => 0) hp () () 0 {()} _ rfl
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalBlockCross_homogeneous
