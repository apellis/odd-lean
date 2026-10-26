import OddMath.QuiverHecke.CyclotomicAction.GlobalRouquierData
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of the Rouquier data on weight spaces of `Λ = 3`: the dot is
odd, the signed crossing is odd and squares to zero. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
example : OddMath.SKM.RouquierData (k := ℚ) (B := cyclotomicActionTarget (k := ℚ)) datum :=
  globalRouquierData datum scalars (fun _ => 0) hp 3
example : (globalRouquierData datum scalars (fun _ => 0) hp 3).dot ()
    (rfl : (-3 : ℤ) + 2 = -3 + 2) ∈ parity (R := ℚ) _ _ 1 :=
  (globalRouquierData datum scalars (fun _ => 0) hp 3).dot_mem () rfl
private theorem e₁ : (-3 : ℤ) + datum.α () = -3 + 2 := rfl
private theorem e₂ : (-3 + 2 : ℤ) + datum.α () = -3 + 2 + 2 := rfl
example : globalActionSignedCross datum scalars (fun _ => 0) hp 3 () () e₁ e₂ e₁ e₂ ≫
    globalActionSignedCross datum scalars (fun _ => 0) hp 3 () () e₁ e₂ e₁ e₂ = 0 :=
  globalActionSignedCross_square datum scalars (fun _ => 0) hp 3 () e₁ e₂
example : (globalRouquierData datum scalars (fun _ => 0) hp 3).cross () () e₁ e₂ e₁ e₂ =
    globalActionSignedCross datum scalars (fun _ => 0) hp 3 () () e₁ e₂ e₁ e₂ := rfl
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalRouquierData_square
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalRouquierData
