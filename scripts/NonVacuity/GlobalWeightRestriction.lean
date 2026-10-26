import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRestriction
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of vacuum restriction and weight-space restriction. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
/-- Restriction from one strand to the empty word, with the vacuum content condition. -/
example : Superfunctor ℚ (GlobalContentModules datum scalars (fun _ => 0) hp {()})
    (GlobalContentModules datum scalars (fun _ => 0) hp 0) :=
  globalContentRestriction datum scalars () (fun _ => 0) hp (add_zero _)
example : heightSuperRestriction datum scalars () (fun _ => 0) hp 1 =
    cyclotomicSuperRestriction datum scalars () (fun _ => 0) hp 0 :=
  heightSuperRestriction_succ datum scalars () (fun _ => 0) hp 0
/-- Weight-space restriction from weight `2 - Λ` to `-Λ`, for `Λ = 3`. -/
example : globalWeightSpace datum scalars (fun _ => 0) hp 3 (-3 + 2) ⟶
    globalWeightSpace datum scalars (fun _ => 0) hp 3 (-3) :=
  globalF datum scalars () (fun _ => 0) hp 3 rfl
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalF
#print axioms OddMath.QuiverHecke.CyclotomicAction.heightSuperRestriction_succ
