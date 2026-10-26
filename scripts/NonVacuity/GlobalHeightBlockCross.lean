import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightBlockCross
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of the block crossing from the empty word: it is odd and
squares to zero. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
example : heightLastCrossing datum scalars (fun _ => 0) () () 0 *
    heightLastCrossing datum scalars (fun _ => 0) () () 0 = 0 :=
  heightLastCrossing_square datum scalars (fun _ => 0) () 0
example : (heightBlockCross datum scalars (fun _ => 0) hp () () 0 0 _ rfl).IsHomogeneous 1 :=
  heightBlockCross_homogeneous datum scalars (fun _ => 0) hp () () 0 0 _ rfl
example : heightBlockCross datum scalars (fun _ => 0) hp () () 0 0 _ rfl ≫
    heightBlockCross datum scalars (fun _ => 0) hp () () 0 0 _ rfl = 0 :=
  heightBlockCross_square datum scalars (fun _ => 0) hp () 0 0 _ rfl
#print axioms OddMath.QuiverHecke.CyclotomicAction.heightBlockCross_square
