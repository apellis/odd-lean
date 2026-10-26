import OddMath.QuiverHecke.CyclotomicAction.GlobalInduction
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of vacuum induction, with a nonzero vacuum image. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
example : Superfunctor ℚ (GlobalContentModules datum scalars (fun _ => 0) hp 0)
    (GlobalContentModules datum scalars (fun _ => 0) hp {()}) :=
  globalContentInduction datum scalars () (fun _ => 0) hp (add_zero _)
example : heightSuperInduction datum scalars () (fun _ => 0) hp 1 =
    cyclotomicSuperInduction datum scalars () (fun _ => 0) hp 0 :=
  heightSuperInduction_succ datum scalars () (fun _ => 0) hp 0
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalContentInduction
#print axioms OddMath.QuiverHecke.CyclotomicAction.heightSuperInduction_succ
