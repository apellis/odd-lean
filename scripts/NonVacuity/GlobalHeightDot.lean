import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightDot
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of the vacuum dot: the dot on induction from the empty word
is odd for the odd colour, and so is its global content restriction. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
example : datum.parity () = 1 := rfl
example : heightLastDot datum scalars (fun _ => 0) () 0 ∈
    heightParity datum scalars (fun _ => 0) hp 1 1 :=
  heightLastDot_parity datum scalars (fun _ => 0) () hp 0
example : (heightSuperInductionDot datum scalars () (fun _ => 0) hp 0).IsHomogeneous 1 :=
  heightSuperInductionDot_homogeneous datum scalars () (fun _ => 0) hp 0
example : (globalContentDot datum scalars () (fun _ => 0) hp (add_zero {()})).IsHomogeneous 1 :=
  globalContentDot_homogeneous datum scalars () (fun _ => 0) hp (add_zero {()})
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalContentDot_homogeneous
#print axioms OddMath.QuiverHecke.CyclotomicAction.heightSuperInductionDot
