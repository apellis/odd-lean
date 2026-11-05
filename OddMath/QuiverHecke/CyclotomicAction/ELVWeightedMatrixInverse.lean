import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixRows
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleMatrixInverse
import Mathlib.LinearAlgebra.Pi
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVParityMatrixCoordinates

/-! # Charts and row comparison for weighted matrices

DeformedMatrixComparison (2), (4) compares the given arbitrary-module old
matrix inverses through the selected append and canonical parity charts.
The conjugate isomorphisms are constructed here; their forward identification
with the finite prescribed weighted matrices is a separate obligation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
section DotComponents
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)

private theorem endpointUnitDotLinear_refl (R : Superfunctor k C (SVec k)) (n : ℕ) (w : C) :
    BalancedInduction.endpointUnitDotLinear J hα R n w (J.obj w) rfl =
      SVec.toLinearMap ((BalancedInduction.unitDotColumn J hα R n).total w) := by
  rw [← BalancedInduction.endpointUnitDotLinear_total J hα R n w (J.obj w) rfl,
    eqToHom_refl, BalancedInduction.postcompose_id, LinearMap.id_comp]

private theorem endpointUnitDot_apply (R : Superfunctor k C (SVec k)) (n : ℕ) (w : C) (b : R.obj w) :
    BalancedInduction.endpointUnitDotLinear J hα R n w (J.obj w) rfl b =
      (BalancedInduction.unitDotColumn J hα R n).total w b :=
  LinearMap.congr_fun (endpointUnitDotLinear_refl J hα R n w) b

private theorem mapComponent_identity (R : Superfunctor k C (SVec k)) (w : A) :
    BalancedInduction.mapComponent J (𝟙 R) 0 w = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro s a b
  rw [BalancedInduction.mapComponent_tensor, twist_zero]
  rfl
end DotComponents

private theorem equiv_hom_apply {k V W : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (e : V ≃ₗ[k] W) (f : V →ₗ[k] W) (h : e.toLinearMap = f) (x : V) :
    e x = f x := LinearMap.congr_fun h x

section FiniteCharts
variable {k : Type u} [CommRing k] {ι : Type} [Fintype ι]
  (V V' : ι → SVec k) (W W' : SVec k)
  (eV : ∀ a, V a ≃ₗ[k] V' a) (eW : W ≃ₗ[k] W')

end FiniteCharts

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "Q" => oldTruncateFunctor D Sc cutoff N
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

private theorem oldUnitColumn_linear
    (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((CyclotomicCrossingTensor.moduleUnitColumn D Sc cutoff i P n).total w) =
      BalancedInduction.unitDotLinear J
        (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) P n w := by
  rw [oldUnitColumn_eq, BalancedInduction.unitDotColumn_total]

private theorem oldUnitColumn_apply
    (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) (w : OldCategory D Sc cutoff) (b : P.obj w) :
    (moduleUnitColumn D Sc cutoff i P n).total w b =
      BalancedInduction.unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) P n w b :=
  LinearMap.congr_fun (oldUnitColumn_linear D Sc cutoff i P n w) b

private theorem oldCapRow_linear
    (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((CyclotomicCrossingTensor.moduleCapRow D Sc cutoff i P n).total w) =
      BalancedInduction.capDotLinear J
        (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cutoff i) P n w := by
  rw [oldCapRow_eq, BalancedInduction.capDotRow_total]

private theorem parity_square (p : ZMod 2) : p * p = p := by
  rcases parity_eq_zero_or_one p with h | h <;> simp only [h, mul_zero, one_mul]

private def oldMateRaw (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J ((BalancedInduction.restriction J).obj P).toFunctor w →ₗ[k]
      BalancedInduction.Obj J P.toFunctor ((J).obj w) :=
  ((oldModuleMate D Sc cutoff i).app (D.parity i * D.parity i) P).total w

private theorem oldMatePrecompose_identity (w : OldCategory D Sc cutoff) :
    weightedOldMatePrecomposeLinear D Sc cutoff N i M ((BalancedInduction.restriction J).obj RM) (𝟙 _) w =
      weightedOldMateLinear D Sc cutoff N i M w := by
  unfold weightedOldMatePrecomposeLinear
  rw [mapComponent_identity, LinearMap.comp_id]

/-- Every prescribed ordinary unit/dot column commutes with the selected value chart. -/
theorem weightedUnitColumnValue_compare (w : OldCategory D Sc cutoff) (n : ℕ) (b : (RM).obj w) :
    weightedMateTargetLinearEquiv D Sc cutoff N i M w
        ((moduleUnitColumn D Sc cutoff i RM n).total w b) =
      (BalancedInduction.unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) M n).total ((Q).obj w) b := by
  have h1 := congrArg (weightedMateTargetLinearEquiv D Sc cutoff N i M w)
    (oldUnitColumn_apply D Sc cutoff i RM n w b)
  have hc := equiv_hom_apply (weightedMateTargetLinearEquiv D Sc cutoff N i M w)
    (weightedAppendComparisonLinear D Sc cutoff N i M ((J).obj w))
    (weightedMateTargetLinearEquiv_hom D Sc cutoff N i M w)
    (BalancedInduction.unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) RM n w b)
  have h2 := LinearMap.congr_fun (weightedMateTargetLinear_unitDot D Sc cutoff N i M w n) b
  have h3 := endpointUnitDot_apply T (truncatedDot_supernatural D Sc cutoff N i) M n ((Q).obj w) b
  have h12 := h1.trans hc
  have h23 := h2.trans h3
  have hresult := h12.trans h23
  exact hresult

/-- Every prescribed ordinary dot/counit row commutes with the selected value chart. -/
theorem weightedCapRowValue_compare (w : OldCategory D Sc cutoff) (n : ℕ)
    (x : ((BalancedInduction.induction J).obj ((BalancedInduction.restriction J).obj RM)).obj w) :
    (moduleCapRow D Sc cutoff i RM n).total w x =
      (BalancedInduction.capDotRow T (truncatedDot_supernatural D Sc cutoff N i) M n).total ((Q).obj w)
        (weightedMateSourceLinearEquiv D Sc cutoff N i M w x) := by
  have h1 := LinearMap.congr_fun (oldCapRow_linear D Sc cutoff i RM n w) x
  have h2 := LinearMap.congr_fun (weightedMateSourceLinear_capDot D Sc cutoff N i M w n) x
  have hc := LinearMap.congr_fun (weightedMateSourceLinearEquiv_hom D Sc cutoff N i M w) x
  have h3 := congrArg
    (BalancedInduction.capDotLinear T (truncatedDot_supernatural D Sc cutoff N i) M n ((Q).obj w)) hc.symm
  have h4 := LinearMap.congr_fun
    (BalancedInduction.capDotRow_total T (truncatedDot_supernatural D Sc cutoff N i) M n ((Q).obj w))
    (weightedMateSourceLinearEquiv D Sc cutoff N i M w x)
  have h23 := h2.symm.trans h3
  have h123 := h1.trans h23
  have hresult := h123.trans h4.symm
  exact hresult

local instance weightedMatrixOldPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory
local instance weightedMatrixQuotientPi : PiSupercategory k (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :=
  supermodulePiSupercategory

/-- Coordinatewise selected source charts with the prescribed module parity actions. -/
def weightedUnitFamilyValueEquiv (m : ℕ) (w : OldCategory D Sc cutoff)
    (a : Option (Fin m)) :
    (CyclotomicCrossingTensor.unitMatrixFamily D Sc cutoff i RM m a).obj w ≃ₗ[k]
      (weightedUnitMatrixFamily D Sc cutoff N i M m a).obj ((Q).obj w) :=
  match a with
  | none => BalancedInduction.shiftedModuleValueLinearEquiv
      ((BalancedInduction.induction J).obj ((BalancedInduction.restriction J).obj RM))
      ((BalancedInduction.induction T).obj ((BalancedInduction.restriction T).obj M))
      w ((Q).obj w) (weightedMateSourceLinearEquiv D Sc cutoff N i M w) (D.parity i)
  | some r => BalancedInduction.shiftedModuleValueLinearEquiv RM M w ((Q).obj w)
      (LinearEquiv.refl k _) (r.val • D.parity i)

/-- Coordinatewise selected target charts with the prescribed module parity actions. -/
def weightedCapFamilyValueEquiv (m : ℕ) (w : OldCategory D Sc cutoff)
    (a : Option (Fin m)) :
    (CyclotomicCrossingTensor.capMatrixFamily D Sc cutoff i RM m a).obj w ≃ₗ[k]
      (weightedCapMatrixFamily D Sc cutoff N i M m a).obj ((Q).obj w) :=
  match a with
  | none => BalancedInduction.shiftedModuleValueLinearEquiv
      ((BalancedInduction.restriction J).obj ((BalancedInduction.induction J).obj RM))
      ((BalancedInduction.restriction T).obj ((BalancedInduction.induction T).obj M))
      w ((Q).obj w) (weightedMateTargetLinearEquiv D Sc cutoff N i M w) (D.parity i)
  | some r => BalancedInduction.shiftedModuleValueLinearEquiv RM M w ((Q).obj w)
      (LinearEquiv.refl k _) (r.val • D.parity i)

/-- The finite source chart is the product of those exact canonical coordinates. -/
def weightedUnitMatrixValueEquiv (m : ℕ) (w : OldCategory D Sc cutoff) :
    CyclotomicCrossingTensor.unitMatrixSourceSpace D Sc cutoff i RM m w ≃ₗ[k]
      weightedUnitMatrixSourceSpace D Sc cutoff N i M m ((Q).obj w) :=
  LinearEquiv.piCongrRight (weightedUnitFamilyValueEquiv D Sc cutoff N i M m w)

/-- The finite target chart is the product of those exact canonical coordinates. -/
def weightedCapMatrixValueEquiv (m : ℕ) (w : OldCategory D Sc cutoff) :
    CyclotomicCrossingTensor.capMatrixTargetSpace D Sc cutoff i RM m w ≃ₗ[k]
      weightedCapMatrixTargetSpace D Sc cutoff N i M m ((Q).obj w) :=
  LinearEquiv.piCongrRight (weightedCapFamilyValueEquiv D Sc cutoff N i M m w)

end OddMath.QuiverHecke.ELVOld
