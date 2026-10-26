import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightDot
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of the weight-space dot: it is odd for the odd colour. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
/-- The dot on `E : -Λ → 2 - Λ`, `Λ = 3`, has odd parity. -/
example : globalActionDot datum scalars (fun _ => 0) hp () 3 (rfl : (-3 : ℤ) + 2 = -3 + 2) ∈
    parity (R := ℚ) (globalActionE datum scalars (fun _ => 0) hp () 3 rfl)
      (globalActionE datum scalars (fun _ => 0) hp () 3 rfl) 1 :=
  globalActionDot_mem datum scalars (fun _ => 0) hp () 3 rfl
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalActionDot_mem
