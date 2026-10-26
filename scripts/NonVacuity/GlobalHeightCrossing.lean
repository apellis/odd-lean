import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightCrossing
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of the crossing on two inductions from the empty word: it is
odd, with parity `|i||i| = 1`. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
example : heightLastCrossing datum scalars (fun _ => 0) () () 0 ∈
    heightParity datum scalars (fun _ => 0) hp 2 1 :=
  heightLastCrossing_parity datum scalars (fun _ => 0) () () hp 0
example : (heightSuperInductionCrossing datum scalars () () (fun _ => 0) hp 0).IsHomogeneous 1 :=
  heightSuperInductionCrossing_homogeneous datum scalars () () (fun _ => 0) hp 0
#print axioms OddMath.QuiverHecke.CyclotomicAction.heightSuperInductionCrossing_homogeneous
