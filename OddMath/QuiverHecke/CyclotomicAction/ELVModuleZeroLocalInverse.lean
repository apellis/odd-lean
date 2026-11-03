import OddMath.QuiverHecke.CyclotomicAction.ELVModuleZeroBoundary
import OddMath.SKM.RouquierBoundary
import OddMath.SKM.RouquierLeftCupCap

/-! # The negative local record at a module vacuum boundary

Brundan–Ellis (1.14): a finite dotted-unit boundary and the canonical
zero lower cell give the local Rouquier record at strictly negative
height. The given upper adjunction, dot and inverse coefficients remain
unchanged; both lower slides follow from the zero lower composite.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  (C : Type u) [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  (B : PiSCat.{u,u,u+1} k)
  {E : inductionModulePiCategory (k := k) C ⟶ B}
  {F : B ⟶ inductionModulePiCategory (k := k) C}
  (A : SKM.SuperAdjunction (k := k) E F) (x : End E) (p : ZMod 2) (m : ℕ)
  (V : SKM.RouquierBoundary.Coefficients A x p m)
local notation "Z" => zeroModuleCell (k := k) C
local notation "A₀" => zeroModuleCellAdjunction (k := k) C

private theorem zeroLowerMate : SKM.rouquierMate A₀ A (0 : End (Z ≫ E)) = 0 := by
  simp only [SKM.rouquierMate, TwoSupercategory.zero_whiskerRight (R := k),
    TwoSupercategory.whiskerLeft_zero (R := k), Limits.comp_zero, Limits.zero_comp]

private def moduleZeroBoundaryInverse :
    SKM.SuperSumInvFrom (k := k) (SKM.rouquierMate A₀ A (0 : End (Z ≫ E)))
      (fun n => A.unit ≫ SKM.rouquierPower x n ▷ F) p (fun n => (n : ZMod 2) * p) m where
  f' := 0
  g' := V.coeff
  f_mem := by rw [zeroLowerMate]; exact Submodule.zero_mem _
  g_mem n := by
    simpa only [zero_add] using
      comp_mem A.unit_mem (TwoSupercategory.whiskerRight_mem F (SKM.rouquierPower_mem V.dot_mem n))
  f'_mem := Submodule.zero_mem _
  g'_mem := V.coeff_mem
  total := by
    rw [Limits.zero_comp, zero_add]
    simpa only [SKM.RouquierBoundary.cup] using V.total
  ff := by
    rw [Limits.comp_zero, zeroModuleCell_comp_id C (inductionModulePiCategory (k := k) C) Z]
  fg n hn := by rw [zeroLowerMate, Limits.zero_comp]
  gf n hn := Limits.comp_zero
  gg := by
    intro j l hj hl
    simpa only [SKM.RouquierBoundary.cup] using V.entry j l hj hl

/-- The existing local Rouquier record at the zero lower edge and negative
boundary height. The coefficient record is an intermediate input, supplied
by the constructed prescribed old vacuum matrix in the concrete adapter. -/
def moduleZeroBoundaryLoc (hm : 0 < m) :
    SKM.SuperRouquierLoc A₀ A (0 : End Z) x (0 : End (Z ≫ E)) p (-(m : ℤ)) where
  dot₁_mem := Submodule.zero_mem _
  dot₂_mem := V.dot_mem
  cross_mem := Submodule.zero_mem _
  slide_left := by
    rw [zeroModuleCell_comp_id C B E]
    simp only [Limits.comp_zero, Limits.zero_comp, smul_zero, sub_zero]
  slide_right := by
    rw [zeroModuleCell_comp_id C B E]
    simp only [Limits.comp_zero, Limits.zero_comp, smul_zero, sub_zero]
  invPos hh := False.elim (by omega)
  invNeg _ := by
    simpa only [neg_neg, Int.toNat_natCast] using moduleZeroBoundaryInverse C B A x p m V

end OddMath.QuiverHecke.ELVOld.BalancedInduction
