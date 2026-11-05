import OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelUnitMatrixEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixBijective

/-! # Prescribed matrix inverses on arbitrary modules

The arbitrary-module inversion step of DeformedMatrixComparison, section 4.
Coefficient-kernel isomorphisms are tensored using the explicit balanced
quotient and transported through the canonical finite shifted coordinates.
The forward maps are the prescribed module matrices. Their independent
evenness implies inverse evenness. No categorical colimit or flatness
hypothesis is used.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))

private theorem opComponents {C : Type u} (P : Cᵒᵖ → Prop)
    (h : ∀ v : C, P (op v)) (v : Cᵒᵖ) : P v := by
  rcases v with ⟨v⟩
  exact h v

private def transportedUnitEquiv (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (hb : ∀ v : OldCategory D Sc cutoff,
      Function.Bijective ((actualPositiveKernelMap D Sc cutoff i m t).app (op v))) :
    unitMatrixSourceSpace D Sc cutoff i M m t ≃ₗ[k] mateTargetSpace D Sc cutoff i M t :=
  (positiveKernelCoordinates D Sc cutoff M i m t).symm.trans
    ((BalancedKernelTensor.equivOfBijective M.toFunctor
      (actualPositiveKernelMap D Sc cutoff i m t)
      (opComponents (fun v => Function.Bijective
        ((actualPositiveKernelMap D Sc cutoff i m t).app v)) hb)).trans
        (resIndKernelCoordinates D Sc cutoff M i t))

private def transportedCapEquiv (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (hb : ∀ v : OldCategory D Sc cutoff,
      Function.Bijective ((actualNegativeKernelMap D Sc cutoff i m t).app (op v))) :
    mateSourceSpace D Sc cutoff i M t ≃ₗ[k] capMatrixTargetSpace D Sc cutoff i M m t :=
  (indResKernelCoordinates D Sc cutoff M i t).symm.trans
    ((BalancedKernelTensor.equivOfBijective M.toFunctor
      (actualNegativeKernelMap D Sc cutoff i m t)
      (opComponents (fun v => Function.Bijective
        ((actualNegativeKernelMap D Sc cutoff i m t).app v)) hb)).trans
        (negativeKernelCoordinates D Sc cutoff M i m t))

private theorem transportedUnitEquiv_apply (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (hb : ∀ v : OldCategory D Sc cutoff,
      Function.Bijective ((actualPositiveKernelMap D Sc cutoff i m t).app (op v)))
    (x : unitMatrixSourceSpace D Sc cutoff i M m t) :
    transportedUnitEquiv D Sc cutoff M i m t hb x = unitMatrixComponent D Sc cutoff i M m t x := by
  change resIndKernelCoordinates D Sc cutoff M i t
      (BalancedKernelTensor.map M.toFunctor (actualPositiveKernelMap D Sc cutoff i m t)
        ((positiveKernelCoordinates D Sc cutoff M i m t).symm x)) = _
  calc
    _ = unitKernelForward D Sc cutoff M i m t
        ((positiveKernelCoordinates D Sc cutoff M i m t).symm x) := rfl
    _ = unitModuleForward D Sc cutoff M i m t
        ((positiveKernelCoordinates D Sc cutoff M i m t).symm x) :=
      LinearMap.congr_fun (unitKernelForward_eq_moduleForward D Sc cutoff M i m t) _
    _ = unitMatrixLinear D Sc cutoff M i m t
        (unitSourceCoordinatesLinear D Sc cutoff M i m t
          ((positiveKernelCoordinates D Sc cutoff M i m t).symm x)) :=
      unitModuleForward_apply D Sc cutoff M i m t _
    _ = unitMatrixComponent D Sc cutoff i M m t x := by
      rw [unitMatrixLinear_apply]
      apply congrArg (unitMatrixComponent D Sc cutoff i M m t)
      exact (positiveKernelCoordinates D Sc cutoff M i m t).apply_symm_apply x

private theorem transportedCapEquiv_apply (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (hb : ∀ v : OldCategory D Sc cutoff,
      Function.Bijective ((actualNegativeKernelMap D Sc cutoff i m t).app (op v)))
    (x : mateSourceSpace D Sc cutoff i M t) :
    transportedCapEquiv D Sc cutoff M i m t hb x = capMatrixComponent D Sc cutoff i M m t x := by
  change negativeKernelCoordinates D Sc cutoff M i m t
      (BalancedKernelTensor.map M.toFunctor (actualNegativeKernelMap D Sc cutoff i m t)
        ((indResKernelCoordinates D Sc cutoff M i t).symm x)) = _
  have h := LinearMap.congr_fun (capKernelForward_eq_moduleForward D Sc cutoff M i m t)
    ((indResKernelCoordinates D Sc cutoff M i t).symm x)
  change negativeKernelCoordinates D Sc cutoff M i m t
      (BalancedKernelTensor.map M.toFunctor (actualNegativeKernelMap D Sc cutoff i m t)
        ((indResKernelCoordinates D Sc cutoff M i t).symm x)) =
    capMatrixComponent D Sc cutoff i M m t
      (indResKernelCoordinates D Sc cutoff M i t
        ((indResKernelCoordinates D Sc cutoff M i t).symm x)) at h
  simpa only [LinearEquiv.apply_symm_apply] using h

/-- The prescribed finite unit matrix is invertible on every old supermodule. -/
def moduleUnitMatrixIso (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) :
    unitMatrixSourceSpace D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) t ≅
        mateTargetSpace D Sc cutoff i M t :=
  SVec.isoOfLinearEquiv (transportedUnitEquiv D Sc cutoff M i
    (contentUnitCount D cutoff i (t.word : Multiset I)) t
      (actualPositiveKernelMap_bijective D Sc cutoff i t hh))

theorem moduleUnitMatrixIso_hom (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) :
    (moduleUnitMatrixIso D Sc cutoff M i t hh).hom =
      unitMatrixComponent D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) t := by
  apply LinearMap.ext
  intro x
  exact transportedUnitEquiv_apply D Sc cutoff M i
    (contentUnitCount D cutoff i (t.word : Multiset I)) t
      (actualPositiveKernelMap_bijective D Sc cutoff i t hh) x

theorem moduleUnitMatrixIso_hom_even (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) :
    (moduleUnitMatrixIso D Sc cutoff M i t hh).hom ∈ parity (R := k)
      (unitMatrixSourceSpace D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) t)
      (mateTargetSpace D Sc cutoff i M t) 0 := by
  rw [moduleUnitMatrixIso_hom]
  exact unitMatrixComponent_even D Sc cutoff i M _ t

theorem moduleUnitMatrixIso_inv_even (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) :
    (moduleUnitMatrixIso D Sc cutoff M i t hh).inv ∈ parity (R := k)
      (mateTargetSpace D Sc cutoff i M t)
      (unitMatrixSourceSpace D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) t) 0 :=
  Supercategory.inv_mem (moduleUnitMatrixIso D Sc cutoff M i t hh)
    (moduleUnitMatrixIso_hom_even D Sc cutoff M i t hh)

/-- The prescribed finite cap matrix is invertible on every old supermodule. -/
def moduleCapMatrixIso (i : I) (t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) :
    mateSourceSpace D Sc cutoff i M t ≅
      capMatrixTargetSpace D Sc cutoff i M
        (contentCapCount D cutoff i (t.word : Multiset I)) t :=
  SVec.isoOfLinearEquiv (transportedCapEquiv D Sc cutoff M i
    (contentCapCount D cutoff i (t.word : Multiset I)) t
      (actualNegativeKernelMap_bijective D Sc cutoff i t hh))

theorem moduleCapMatrixIso_hom (i : I) (t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) :
    (moduleCapMatrixIso D Sc cutoff M i t hh).hom =
      capMatrixComponent D Sc cutoff i M
        (contentCapCount D cutoff i (t.word : Multiset I)) t := by
  apply LinearMap.ext
  intro x
  exact transportedCapEquiv_apply D Sc cutoff M i
    (contentCapCount D cutoff i (t.word : Multiset I)) t
      (actualNegativeKernelMap_bijective D Sc cutoff i t hh) x

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
