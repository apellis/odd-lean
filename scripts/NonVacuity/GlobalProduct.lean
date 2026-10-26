import OddMath.QuiverHecke.CyclotomicAction.GlobalProduct
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
example : Nonempty (WeightBlocks datum (0 : ℤ) 0) := ⟨⟨0, by simp⟩⟩
#check globalWeightSpace datum scalars (fun _ => 0) hp (0 : ℤ) 0
#print axioms OddMath.QuiverHecke.CyclotomicAction.productSupercategory
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalWeightSpace
