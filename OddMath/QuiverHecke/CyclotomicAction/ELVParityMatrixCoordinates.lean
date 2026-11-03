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

/-- Exact canonical source/chart/target chain on the original module values. -/
theorem shiftedModuleValueLinearEquiv_apply (q : ZMod 2)
    (b : ((SKM.homParityShift (k := k) q).obj M).obj w) :
    shiftedModuleValueLinearEquiv M N w v e q b =
      ((SKM.homParityShiftDatum (k := k) q).iso N).inv.total v
        (e (((SKM.homParityShiftDatum (k := k) q).iso M).hom.total w b)) := rfl

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

private theorem value_total_mem
    {A : Type u} [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : Superfunctor k A (SVec k)} {q : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ q) (a : A) :
    f.total a ∈ parity (R := k) (F.obj a) (G.obj a) q := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · have hz := Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) a
    rw [SuperNatTrans.total, hz, add_zero]
    exact f.app_mem 0 a
  · have hz := Superfunctor.app_eq_zero_of_mem hf (by decide : (0 : ZMod 2) ≠ 1) a
    rw [SuperNatTrans.total, hz, zero_add]
    exact f.app_mem 1 a

/-- Even selected plain charts give even charts on the actual shifted values. -/
theorem shiftedModuleValueLinearEquiv_hom_mem (q : ZMod 2)
    (he : SVec.ofHom e.toLinearMap ∈ parity (R := k) (M.obj w) (N.obj v) 0) :
    SVec.ofHom (shiftedModuleValueLinearEquiv M N w v e q).toLinearMap ∈
      parity (R := k) _ _ 0 := by
  change (((SKM.homParityShiftDatum (k := k) q).iso M).hom.total w ≫
    SVec.ofHom e.toLinearMap ≫ ((SKM.homParityShiftDatum (k := k) q).iso N).inv.total v) ∈ _
  have h := comp_mem
    (value_total_mem ((SKM.homParityShiftDatum (k := k) q).hom_mem M) w)
    (comp_mem he (value_total_mem ((SKM.homParityShiftDatum (k := k) q).inv_mem N) v))
  simpa only [zero_add, SKM.zmod2_add_self] using h

/-- The inverse uses those same canonical coordinates and is even. -/
theorem shiftedModuleValueLinearEquiv_inv_mem (q : ZMod 2)
    (he : SVec.ofHom e.toLinearMap ∈ parity (R := k) (M.obj w) (N.obj v) 0) :
    SVec.ofHom (shiftedModuleValueLinearEquiv M N w v e q).symm.toLinearMap ∈
      parity (R := k) _ _ 0 :=
  inv_mem (SVec.isoOfLinearEquiv (shiftedModuleValueLinearEquiv M N w v e q))
    (shiftedModuleValueLinearEquiv_hom_mem M N w v e q he)

end OddMath.QuiverHecke.ELVOld.BalancedInduction
