import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightAdjunction
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of the weight-space adjunction, from the vacuum weight. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
/-- `E ⊣ F` between the weights `-Λ` and `2 - Λ` for `Λ = 3`, as a super adjunction. -/
example : OddMath.SKM.SuperAdjunction (k := ℚ)
    (globalActionE datum scalars (fun _ => 0) hp () 3 (rfl : (-3 : ℤ) + 2 = -3 + 2))
    (globalActionF datum scalars (fun _ => 0) hp () 3 (rfl : (-3 : ℤ) + 2 = -3 + 2)) :=
  globalActionAdjunction datum scalars (fun _ => 0) hp () 3 rfl
/-- The weight-space unit is even. -/
example (M : WeightProduct datum scalars (fun _ => 0) hp 3 (-3)) :
    (globalWeightUnit datum scalars (fun _ => 0) hp () 3
      (rfl : (-3 : ℤ) + 2 = -3 + 2)).app M ∈ parity (R := ℚ) _ _ 0 :=
  globalWeightUnit_mem datum scalars (fun _ => 0) hp () 3 rfl M
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalActionAdjunction
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalWeightAdjunction
