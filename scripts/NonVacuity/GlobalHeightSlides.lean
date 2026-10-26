import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightSlides
import OddMath.QuiverHecke.CyclotomicAction.VacuumExamples

/-! Odd rank-one specialization of the corner and functor slides: the colour is odd, so
`s = -1` and the slides read `ψ y₁ + y₂ ψ = -1` and `y₁ ψ + ψ y₂ = -1`. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.Examples
private theorem hp : CyclotomicPolynomialParity datum (fun _ => (0 : Polynomial ℚ)) := by
  intro i m h
  simp at h
example : vacuumAppend datum scalars () (fun _ => 0) 1 ≠ 0 := VacuumExamples.vacuum_unit_ne_zero
example :
    heightCompositionSuperCrossing datum scalars () () (fun _ => 0) hp 0 ≫
        heightCompositionRightMul datum scalars () (fun _ => 0) hp 0
          (cornerMulData_appendDot datum scalars () (fun _ => 0) hp 0) +
      heightCompositionRightMul datum scalars () (fun _ => 0) hp 0
          (cornerMulData_lastDot datum scalars () (fun _ => 0) hp 0) ≫
        heightCompositionSuperCrossing datum scalars () () (fun _ => 0) hp 0 = -𝟙 _ := by
  have h := heightCompositionCorner_slide_left datum scalars () (fun _ => 0) hp 0
  simpa only [show datum.parity () = 1 from rfl, koszulSign_one_one, neg_smul, one_smul,
    sub_neg_eq_add] using h
private abbrev FF (M : HeightModules datum scalars (fun _ => (0 : Polynomial ℚ)) hp 0) :=
  (heightSuperInduction datum scalars () (fun _ => (0 : Polynomial ℚ)) hp 1).obj
  ((heightSuperInduction datum scalars () (fun _ => (0 : Polynomial ℚ)) hp 0).obj M)
example (M : HeightModules datum scalars (fun _ => (0 : Polynomial ℚ)) hp 0) :
    ((heightSuperInduction datum scalars () (fun _ => 0) hp 1).map
      ((heightSuperInductionDot datum scalars () (fun _ => 0) hp 0).app 1 M) ≫
        (heightSuperInductionCrossing datum scalars () () (fun _ => 0) hp 0).app (1 * 1) M :
        FF M ⟶ FF M) +
      ((heightSuperInductionCrossing datum scalars () () (fun _ => 0) hp 0).app (1 * 1) M ≫
        (heightSuperInductionDot datum scalars () (fun _ => 0) hp 1).app 1
          ((heightSuperInduction datum scalars () (fun _ => 0) hp 0).obj M) :
        FF M ⟶ FF M) = -𝟙 _ := by
  have h := heightInduction_slide_right datum scalars () (fun _ => 0) hp 0 M
  simpa only [show datum.parity () = 1 from rfl, koszulSign_one_one, neg_smul, one_smul,
    sub_neg_eq_add] using h
#print axioms OddMath.QuiverHecke.CyclotomicAction.heightInduction_slide_left
#print axioms OddMath.QuiverHecke.CyclotomicAction.heightInduction_slide_right
