/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.FiniteModuleLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMatrixFamilies

/-! # Local inverse entries of the prescribed induction-grid matrices

BE (1.13)–(1.14): the inverse of the specified even finite grid matrix
supplies the local inverse entries of its given mate and ordinary dotted
unit or cap fields, retaining the canonical parity coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.FiniteSupermodule
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
  (N : Superfunctor k A (SVec k)) (m : ℕ)
local instance gridLocalModulePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory

/-- The given unit matrix inverse supplies every local inverse field of its
specified mate and unit/dot columns. The matrix isomorphism is an intermediate input. -/
def gridLocalInverseFrom
    (e : product (gridUnitMatrixFamily J p N m) ≅ (restriction K).obj (induced K N))
    (he : e.hom = gridUnitMatrixModuleMap J K hγ hβ N m) :
    SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent J K hγ N)
      (unitDotColumn K hβ N) p (fun n => n • p) m :=
  localInverseFromColumns p (fun n => n • p)
    ((SKM.homParityShiftDatum (k := k) p).iso (induced J ((restriction J).obj N)))
    (fun r => (SKM.homParityShiftDatum (k := k) (r.val • p)).iso N)
    ((SKM.homParityShiftDatum (k := k) p).hom_mem _)
    (fun r => (SKM.homParityShiftDatum (k := k) (r.val • p)).hom_mem N)
    (orderedGridMateComponent J K hγ N) (unitDotColumn K hβ N)
    (orderedGridMateComponent_mem J K hγ N) (unitDotColumn_mem K hβ N) e (by
      have hc : restoredColumn
          (optionRestoringIso
            ((SKM.homParityShiftDatum (k := k) p).iso (induced J ((restriction J).obj N)))
            (fun r => (SKM.homParityShiftDatum (k := k) (r.val • p)).iso N))
          (optionForwardColumns (orderedGridMateComponent J K hγ N) (unitDotColumn K hβ N)) =
          gridUnitMatrixEntry J K hγ hβ N m := by
        funext a
        cases a <;> rfl
      rw [he, restoredColumns, gridUnitMatrixModuleMap]
      simp only [hc])

/-- The given cap matrix inverse supplies every local inverse field of its
specified mate and dot/counit rows. The matrix isomorphism is an intermediate input. -/
def gridLocalInverseTo
    (e : induced J ((restriction J).obj N) ≅ product (gridCapMatrixFamily K p N m))
    (he : e.hom = gridCapMatrixModuleMap J K hγ hα N m) :
    SKM.SuperSumInvTo (k := k) (orderedGridMateComponent J K hγ N)
      (capDotRow J hα N) p (fun n => n • p) m :=
  localInverseToRows p (fun n => n • p)
    ((SKM.homParityShiftDatum (k := k) p).iso ((restriction K).obj (induced K N)))
    (fun r => (SKM.homParityShiftDatum (k := k) (r.val • p)).iso N)
    ((SKM.homParityShiftDatum (k := k) p).hom_mem _)
    (fun r => (SKM.homParityShiftDatum (k := k) (r.val • p)).hom_mem N)
    (orderedGridMateComponent J K hγ N) (capDotRow J hα N)
    (orderedGridMateComponent_mem J K hγ N) (capDotRow_mem J hα N) e (by
      have hc : restoredRow
          (optionRestoringIso
            ((SKM.homParityShiftDatum (k := k) p).iso ((restriction K).obj (induced K N)))
            (fun r => (SKM.homParityShiftDatum (k := k) (r.val • p)).iso N))
          (optionForwardRows (orderedGridMateComponent J K hγ N) (capDotRow J hα N)) =
          gridCapMatrixEntry J K hγ hα N m := by
        funext a
        cases a <;> rfl
      rw [he, restoredRows, gridCapMatrixModuleMap]
      simp only [hc])

end OddMath.QuiverHecke.ELVOld.BalancedInduction
