import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMateTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform
import Mathlib.CategoryTheory.EqToHom
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeOrdinaryAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeQuotientInduction
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform
import Mathlib.CategoryTheory.EqToHom
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
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

private theorem shiftedRestriction_total {L L' : Superfunctor k B (SVec k)}
    (f : L ⟶ L') (w : A) : ((restriction Q).map f).total w = f.total (Q.obj w) := rfl

/-- The canonical parity-coordinate square on actual module values. -/
theorem parityRestrictionIso_inv_coordinate_total (q : ZMod 2)
    (he : e.hom ∈ parity (R := k) _ _ 0) (w : A) :
    SVec.toLinearMap ((parityRestrictionIso Q M N e q).hom.total w) ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso M).inv.total (Q.obj w)) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso N).inv.total w) ∘ₗ
        SVec.toLinearMap (e.hom.total w) := by
  have h := congrArg (fun f => SVec.toLinearMap (f.total w))
    (parityRestrictionIso_inv_coordinate Q M N e q he)
  simpa only [Superfunctor.comp_total, SVec.toLinearMap_comp, shiftedRestriction_total] using h

end Coordinates

private theorem shiftedCapTransport
    {k V W X Y V' W' : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    [AddCommMonoid V'] [Module k V'] [AddCommMonoid W'] [Module k W']
    (C : V →ₗ[k] W) (a : V →ₗ[k] X) (b : W →ₗ[k] Y)
    (v : Y →ₗ[k] X) (zX : X →ₗ[k] V') (zY : Y →ₗ[k] W') (S : W' →ₗ[k] V')
    (hrow : v ∘ₗ b ∘ₗ C = a) (hz : S ∘ₗ zY = zX ∘ₗ v) :
    S ∘ₗ (zY ∘ₗ b) ∘ₗ C = zX ∘ₗ a := by
  ext x
  exact (LinearMap.congr_fun hz (b (C x))).trans
    (congrArg zX (LinearMap.congr_fun hrow x))

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

/-- An actual dot/counit comparison transports to its prescribed canonical
shifted targets through the full parity/restriction module isomorphism. -/
theorem shiftedCapDotLinear_compare (he : e.hom ∈ parity (R := k) _ _ 0)
    (n : ℕ) (w : A)
    (c : Obj J ((restriction J).obj N).toFunctor w →ₗ[k]
      Obj T ((restriction T).obj M).toFunctor (Q.obj w))
    (hrow : SVec.toLinearMap (e.hom.total w) ∘ₗ capDotLinear T hβ M n (Q.obj w) ∘ₗ c =
      capDotLinear J hα N n w) :
    SVec.toLinearMap ((parityRestrictionIso Q M N e (n • p)).hom.total w) ∘ₗ
        shiftedCapDotLinear T hβ M n (Q.obj w) ∘ₗ c =
      shiftedCapDotLinear J hα N n w :=
  shiftedCapTransport c (capDotLinear J hα N n w) (capDotLinear T hβ M n (Q.obj w))
    (SVec.toLinearMap (e.hom.total w))
    (SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (n • p)).iso N).inv.total w))
    (SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (n • p)).iso M).inv.total (Q.obj w)))
    (SVec.toLinearMap ((parityRestrictionIso Q M N e (n • p)).hom.total w)) hrow
    (parityRestrictionIso_inv_coordinate_total Q M N e (n • p) he w)

end Comparison
end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u

private theorem shiftedEqIso_mem
    {k A : Type u} [CommRing k] [Category.{u} A] [Preadditive A] [Linear k A]
    [Supercategory k A] {F G : Superfunctor k A (SVec k)} (h : F = G) :
    (eqToIso h).hom ∈ parity (R := k) _ _ 0 := by
  cases h
  exact id_mem F

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

/-- The checked scalar cap square evaluated on the actual dot-power/counit
module rows. Their canonical parity targets are attached below. -/
theorem probeMappedAppendLinear_capDotRow
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (n : ℕ) :
    SVec.toLinearMap ((e).hom.total w) ∘ₗ
        capDotLinear T (probeOrdinaryAppendDot_supernatural D Sc m ν i) O n ((U).obj w) ∘ₗ
        probeMappedAppendLinear D Sc m ν R hR ((restriction T).obj O) c i w =
      capDotLinear J (probeOldContentAppendDot_supernatural D Sc m ν i) N n w := by
  have h := probeMappedAppendLinear_capRow D Sc m ν i N hN w n
  exact h

/-- Every prescribed scalar cap row commutes with the actual canonical
parity-target module comparison, with no rescaling of the dotted row. -/
theorem probeMappedAppendLinear_shiftedCapRow
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (n : ℕ) :
    SVec.toLinearMap ((parityRestrictionIso U O N e (n • D.parity i)).hom.total w) ∘ₗ
        shiftedCapDotLinear T (probeOrdinaryAppendDot_supernatural D Sc m ν i) O n ((U).obj w) ∘ₗ
        probeMappedAppendLinear D Sc m ν R hR ((restriction T).obj O) c i w =
      shiftedCapDotLinear J (probeOldContentAppendDot_supernatural D Sc m ν i) N n w :=
  shiftedCapDotLinear_compare J T U
    (probeOldContentAppendDot_supernatural D Sc m ν i)
    (probeOrdinaryAppendDot_supernatural D Sc m ν i) O N e
    (shiftedEqIso_mem (probeOrdinaryModuleSuperfunctor_restrict D Sc m (i :: ν) N hN)) n w
    (probeMappedAppendLinear D Sc m ν R hR ((restriction T).obj O) c i w)
    (probeMappedAppendLinear_capDotRow D Sc m ν i N hN w n)

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance capMatrixEntryComparisonPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- On the actual old append functor this is exactly the prescribed finite
cap-matrix field, whose normalized kernel formula is already fixed. -/
theorem capMatrixEntry_some_eq_shiftedCapDotRow (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (r : Fin m) :
    capMatrixEntry D Sc cutoff i M m (some r) =
      BalancedInduction.shiftedCapDotRow (append D Sc cutoff i)
        (oldAppendDot_supernatural D Sc cutoff i) M r.val := rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
