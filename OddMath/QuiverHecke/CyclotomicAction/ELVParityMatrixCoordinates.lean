import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations
import OddMath.SKM.RouquierNormalizedHomAdjunction

/-! # Canonical parity coordinates for the prescribed finite matrix charts

DeformedMatrixComparison (4), (5) compares finite families of actual shifted
module values. The point chart below first removes the given source parity
coordinate, applies the selected unshifted chart, and inserts the given
target parity coordinate. The module categories and evaluation objects may
be different; their full parity actions are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (M : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
  (w : C) (v : D) (e : M.obj w ≃ₗ[k] N.obj v)
local instance parityMatrixSourcePi : PiSupercategory k (Superfunctor k C (SVec k)) := supermodulePiSupercategory
local instance parityMatrixTargetPi : PiSupercategory k (Superfunctor k D (SVec k)) := supermodulePiSupercategory

/-- The selected value chart conjugated by the existing module parity coordinates. -/
def shiftedModuleValueLinearEquiv (q : ZMod 2) :
    ((SKM.homParityShift (k := k) q).obj M).obj w ≃ₗ[k]
      ((SKM.homParityShift (k := k) q).obj N).obj v :=
  (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) q).iso M) w).trans
    (e.trans (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) q).iso N) v).symm)

/-- Removing the target coordinate recovers exactly the chosen plain chart. -/
theorem shiftedModuleValueLinearEquiv_hom_coordinate (q : ZMod 2)
    (b : ((SKM.homParityShift (k := k) q).obj M).obj w) :
    ((SKM.homParityShiftDatum (k := k) q).iso N).hom.total v
        (shiftedModuleValueLinearEquiv M N w v e q b) =
      e (((SKM.homParityShiftDatum (k := k) q).iso M).hom.total w b) := by
  exact (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) q).iso N) v).apply_symm_apply _

/-- Inserting the source coordinate commutes with the same chosen plain chart. -/
theorem shiftedModuleValueLinearEquiv_inv_coordinate (q : ZMod 2) (b : M.obj w) :
    shiftedModuleValueLinearEquiv M N w v e q
        (((SKM.homParityShiftDatum (k := k) q).iso M).inv.total w b) =
      ((SKM.homParityShiftDatum (k := k) q).iso N).inv.total v (e b) := by
  exact congrArg (fun x =>
    (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) q).iso N) v).symm (e x))
      ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) q).iso M) w).apply_symm_apply b)

end OddMath.QuiverHecke.ELVOld.BalancedInduction
