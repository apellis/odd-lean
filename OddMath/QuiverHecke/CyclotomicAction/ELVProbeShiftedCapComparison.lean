import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMateTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridComposition
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeQuotientInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridComposition
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionDoubleTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRestrictionComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVOperatorPowerComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction
import OddMath.SKM.RouquierNormalizedHomAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixRows

/-! # Prescribed cap rows with their canonical parity targets

DeformedMatrixComparison (2), (5) uses the actual dot-power/counit module
rows, followed by the canonical target parity coordinate. This module keeps
the given module parity actions and transports that coordinate through the
selected scalar comparison; no rescaling of a dotted cap is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
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
end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
local notation "J" => ELVOld.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN
local notation "R" => Functor.obj (restriction J) N
local notation "hR" => probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN
local notation "c" => eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)
local notation "e" => eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m (i :: ν) N hN)
local instance scalarShiftedCapOldPi : PiSupercategory k
    (Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k)) :=
  supermodulePiSupercategory
local instance scalarShiftedCapOrdinaryPi : PiSupercategory k
    (Superfunctor k (OrdinaryContentCategory D Sc
      (probePolynomial (k := k) (probeDotExponent D) m) (i :: ν)) (SVec k)) :=
  supermodulePiSupercategory

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance capMatrixEntryComparisonPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
