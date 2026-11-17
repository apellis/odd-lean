import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Category.ModuleCat.Basic
import OddMath.QuiverHecke.CyclotomicAction.ProbeScalarModules.ProbeOrdinaryCategory
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts.UnitCoefficientRows

/-!
# Probe vacuum charts

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Prescribed cap rows with their canonical parity targets

DeformedMatrixComparison (2), (5) uses the actual dot-power/counit module
rows, followed by the canonical target parity coordinate. This module keeps
the given module parity actions and transports that coordinate through the
selected scalar comparison; no rescaling of a dotted cap is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u

section ShiftedRows
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
local instance shiftedCapRowsModulePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory

/-- The prescribed dot/counit row with its actual canonical shifted target. -/
def shiftedCapDotRow (N : Superfunctor k A (SVec k)) (n : ℕ) :
    (induction J).obj ((restriction J).obj N) ⟶
      (SKM.homParityShift (k := k) (n • p)).obj N :=
  capDotRow J hα N n ≫ ((SKM.homParityShiftDatum (k := k) (n • p)).iso N).inv

theorem shiftedCapDotRow_mem (N : Superfunctor k A (SVec k)) (n : ℕ) :
    shiftedCapDotRow J hα N n ∈ parity (R := k) _ _ 0 := by
  simpa only [shiftedCapDotRow, SKM.zmod2_add_self] using
    comp_mem (capDotRow_mem J hα N n)
      ((SKM.homParityShiftDatum (k := k) (n • p)).inv_mem N)

/-- Raw component of the given shifted module row, with its dictionaries fixed
before specializing a category or module. -/
def shiftedCapDotLinear (N : Superfunctor k A (SVec k)) (n : ℕ) (w : A) :
    Obj J ((restriction J).obj N).toFunctor w →ₗ[k]
      ((SKM.homParityShift (k := k) (n • p)).obj N).obj w :=
  SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (n • p)).iso N).inv.total w) ∘ₗ
    capDotLinear J hα N n w

theorem shiftedCapDotRow_total (N : Superfunctor k A (SVec k)) (n : ℕ) (w : A) :
    SVec.toLinearMap ((shiftedCapDotRow J hα N n).total w) =
      shiftedCapDotLinear J hα N n w := by
  rw [shiftedCapDotRow, Superfunctor.comp_total, SVec.toLinearMap_comp, capDotRow_total]
  rfl

end ShiftedRows

section Coordinates
variable {k A B : Type u} [CommRing k] [Category.{u} A] [Category.{u} B]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (Q : A ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (M : Superfunctor k B (SVec k)) (N : Superfunctor k A (SVec k))
  (e : (restriction Q).obj M ≅ N)
local instance shiftedCapCoordinateSourcePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory
local instance shiftedCapCoordinateTargetPi : PiSupercategory k (Superfunctor k B (SVec k)) :=
  supermodulePiSupercategory

end Coordinates

section Comparison
variable {k C A D B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} D] [Preadditive D] [Linear k D] [Supercategory k D]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (T : D ⥤ B) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (Q : A ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, T.obj s ⟶ T.obj s} (hβ : IsSupernatural k p β)
  (M : Superfunctor k B (SVec k)) (N : Superfunctor k A (SVec k))
  (e : (restriction Q).obj M ≅ N)
local instance shiftedCapComparisonSourcePi : PiSupercategory k (Superfunctor k A (SVec k)) := supermodulePiSupercategory
local instance shiftedCapComparisonTargetPi : PiSupercategory k (Superfunctor k B (SVec k)) := supermodulePiSupercategory

end Comparison
end OddMath.QuiverHecke.ELV.BalancedInduction

namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
local instance scalarShiftedCapOldPi : PiSupercategory k
    (Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k)) :=
  supermodulePiSupercategory
local instance scalarShiftedCapOrdinaryPi : PiSupercategory k
    (Superfunctor k (OrdinaryContentCategory D Sc
      (probePolynomial (k := k) (probeDotExponent D) m) (i :: ν)) (SVec k)) :=
  supermodulePiSupercategory

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance capMatrixEntryComparisonPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Canonical parity coordinates for the prescribed finite matrix charts

DeformedMatrixComparison (4), (5) compares finite families of actual shifted
module values. The point chart below first removes the given source parity
coordinate, applies the selected unshifted chart, and inserts the given
target parity coordinate. The module categories and evaluation objects may
be different; their full parity actions are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
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

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end
