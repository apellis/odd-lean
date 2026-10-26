import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightAdjunction
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of the vacuum adjunction: induction from the empty word
to one strand is left adjoint to restriction, with even unit. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
example : (globalContentInduction datum scalars () (fun _ => 0) hp (add_zero {()})).toFunctor ⊣
    (globalContentRestriction datum scalars () (fun _ => 0) hp (add_zero {()})).toFunctor :=
  globalContentAdjunction datum scalars () (fun _ => 0) hp (add_zero {()})
example (M : ObjectProperty.FullSubcategory
    (heightContentSupported datum scalars (fun _ => 0) hp 0 (0 : Multiset Unit))) :
    (heightContentUnit datum scalars () (fun _ => 0) hp 0 0 rfl).app M ∈
      Supercategory.parity (R := ℚ) _ _ 0 :=
  heightContentUnit_mem datum scalars () (fun _ => 0) hp 0 0 rfl M
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalContentAdjunction
#print axioms OddMath.QuiverHecke.CyclotomicAction.heightSuperRestriction_triangle
