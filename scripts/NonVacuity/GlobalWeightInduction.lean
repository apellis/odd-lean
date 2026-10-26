import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightInduction
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of weight-space induction: the vacuum successor component
and a component with no predecessor. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
/-- Weight-space induction from weight `-Λ` to `2 - Λ`, for `Λ = 3`. -/
example : globalWeightSpace datum scalars (fun _ => 0) hp 3 (-3) ⟶
    globalWeightSpace datum scalars (fun _ => 0) hp 3 (-3 + 2) :=
  globalE datum scalars (fun _ => 0) hp () 3 rfl
/-- At the successor of the empty content the component is vacuum induction. -/
example (β : WeightBlocks datum 3 (-3)) :
    inductionComponent datum scalars (fun _ => 0) hp () 3 (rfl : (-3 : ℤ) + 2 = -3 + 2)
        (blockSucc datum 3 () rfl β) =
      (blockEval datum scalars (fun _ => 0) hp 3 β).comp
        (globalContentInduction datum scalars () (fun _ => 0) hp
          (blockSucc_val datum 3 () rfl β).symm) :=
  inductionComponent_blockSucc datum scalars (fun _ => 0) hp () 3 rfl β
/-- The empty content has no predecessor, so its component is zero. -/
example (M : WeightProduct datum scalars (fun _ => 0) hp 3 (-5))
    (hδ : blockWeight datum 3 0 = -5 + 2) :
    Limits.IsZero ((inductionComponent datum scalars (fun _ => 0) hp () 3
      (rfl : (-5 : ℤ) + 2 = -5 + 2) ⟨0, hδ⟩).obj M) := by
  apply inductionComponent_isZero
  rintro ⟨β, hβ⟩
  have h0 : ({()} : Multiset Unit) + β.1 = 0 := blockSucc_eq datum 3 () hβ
  simp at h0
#print axioms OddMath.QuiverHecke.CyclotomicAction.globalE
#print axioms OddMath.QuiverHecke.CyclotomicAction.inductionComponent_isZero
#print axioms OddMath.QuiverHecke.CyclotomicAction.inductionComponent_blockSucc
