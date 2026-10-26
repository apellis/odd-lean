import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightCross
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of the weight-space crossing `E E ⟶ E E : -Λ → 4 - Λ`,
`Λ = 3`: it is odd, with parity `|i||i| = 1`. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
example : globalActionCross datum scalars (fun _ => 0) hp () () 3 (rfl : (-3 : ℤ) + 2 = -3 + 2)
    (rfl : (-3 + 2 : ℤ) + 2 = -3 + 2 + 2) (rfl : (-3 : ℤ) + 2 = -3 + 2)
    (rfl : (-3 + 2 : ℤ) + 2 = -3 + 2 + 2) ∈ parity (R := ℚ) _ _ 1 :=
  globalActionCross_mem datum scalars (fun _ => 0) hp () () 3 _ _ _ _
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalActionCross_mem
