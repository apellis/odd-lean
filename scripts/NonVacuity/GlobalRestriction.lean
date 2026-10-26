import OddMath.QuiverHecke.CyclotomicAction.GlobalRestriction
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of the block adjunction. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
example : (globalBlockInduction datum scalars (fun _ => 0) hp () 0 {()}).toFunctor ⊣
    (globalBlockRestriction datum scalars (fun _ => 0) hp () 0 {()}).toFunctor :=
  globalBlockAdjunction datum scalars (fun _ => 0) hp () 0 {()}
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalBlockAdjunction
