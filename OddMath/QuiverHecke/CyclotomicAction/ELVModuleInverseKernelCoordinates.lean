import OddMath.QuiverHecke.CyclotomicAction.ELVModuleMatrixInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixInteger

/-! # The selected OLD matrix inverse in balanced kernel coordinates

These equations expose the inverse hidden by the module-matrix construction,
including its action on every pure tensor and the principal finite slot.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
namespace BalancedKernelTensor
variable {k C : Type u} [CommRing k] [Category.{u} C]
  (M : C ⥤ SVec k) {K L : Cᵒᵖ ⥤ ModuleCat k}

/-- The tensor inverse uses the inverse of the actual coefficient map on
its kernel factor, without a flatness or projectivity premise. -/
theorem equivOfBijective_symm_tensor (e : K ⟶ L)
    (he : ∀ v, Function.Bijective (e.app v)) (v : C) (a : L.obj (op v)) (b : M.obj v) :
    (equivOfBijective M e he).symm (tensor L M v a b) =
      tensor K M v ((LinearEquiv.ofBijective (e.app (op v)).hom (he (op v))).symm a) b := by
  exact map_tensor M (coefficientIso e he).inv v a b
end BalancedKernelTensor
namespace CyclotomicCrossingTensor.TensorMatrixCoordinates
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
  (i : I) (t : OldCategory D Sc cutoff)

/-- The selected OLD unit-matrix inverse is the balanced tensor kernel inverse
in the prescribed finite shifted coordinates. -/
theorem moduleUnitMatrixIso_inv_kernel
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (z : mateTargetSpace D Sc cutoff i M t) :
    (moduleUnitMatrixIso D Sc cutoff M i t hh).inv z =
      positiveKernelCoordinates D Sc cutoff M i _ t
        ((BalancedKernelTensor.equivOfBijective M.toFunctor
          (actualPositiveKernelMap D Sc cutoff i _ t)
          (fun v => by
            rcases v with ⟨v⟩
            exact actualPositiveKernelMap_bijective D Sc cutoff i t hh v)).symm
          ((resIndKernelCoordinates D Sc cutoff M i t).symm z)) := rfl

/-- The selected OLD cap-matrix inverse uses the actual negative kernel map. -/
theorem moduleCapMatrixIso_inv_kernel
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (z : capMatrixTargetSpace D Sc cutoff i M (contentCapCount D cutoff i (t.word : Multiset I)) t) :
    (moduleCapMatrixIso D Sc cutoff M i t hh).inv z =
      indResKernelCoordinates D Sc cutoff M i t
        ((BalancedKernelTensor.equivOfBijective M.toFunctor
          (actualNegativeKernelMap D Sc cutoff i _ t)
          (fun v => by
            rcases v with ⟨v⟩
            exact actualNegativeKernelMap_bijective D Sc cutoff i t hh v)).symm
          ((negativeKernelCoordinates D Sc cutoff M i _ t).symm z)) := rfl

/-- On pure upper-Hom tensors the unit inverse applies the raw coefficient
inverse and leaves the module vector unchanged. -/
theorem moduleUnitMatrixIso_inv_tensor
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (v : OldCategory D Sc cutoff)
    (y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) (b : M.obj v) :
    (moduleUnitMatrixIso D Sc cutoff M i t hh).inv
      (BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v y b) =
    positiveKernelCoordinates D Sc cutoff M i _ t
      (BalancedKernelTensor.tensor _ M.toFunctor v
        ((positiveKernelEquiv D Sc cutoff i v t hh).symm y) b) := by
  rw [moduleUnitMatrixIso_inv_kernel, ← resIndKernelCoordinates_tensor,
    LinearEquiv.symm_apply_apply, BalancedKernelTensor.equivOfBijective_symm_tensor]
  rfl

/-- Removing the prescribed principal source parity shift identifies the OLD
unit principal inverse with the raw positive kernel principal inverse. -/
theorem moduleUnitMatrixIso_principal_inv_tensor
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (v : OldCategory D Sc cutoff)
    (y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) (b : M.obj v) :
    moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I))) t
      (((moduleUnitMatrixIso D Sc cutoff M i t hh).inv
        (BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v y b)) none) =
    IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t b
      (positiveKernelPrincipalInverse D Sc cutoff i v t hh y) := by
  rw [moduleUnitMatrixIso_inv_tensor, positiveKernelCoordinates_apply,
    BalancedKernelTensor.map_tensor, positiveSlotCoordinates_none]
  change indResKernelCoordinates D Sc cutoff M i t
    (BalancedKernelTensor.tensor (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
      M.toFunctor v (positiveKernelPrincipalInverse D Sc cutoff i v t hh y) b) = _
  exact indResKernelCoordinates_tensor D Sc cutoff M i v t _ b

/-- The cap inverse likewise acts on the raw finite coefficient family. -/
theorem moduleCapMatrixIso_inv_tensor
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (v : OldCategory D Sc cutoff)
    (y : (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t)).obj (op v)) (b : M.obj v) :
    (moduleCapMatrixIso D Sc cutoff M i t hh).inv
      (negativeKernelCoordinates D Sc cutoff M i _ t
        (BalancedKernelTensor.tensor _ M.toFunctor v y b)) =
    IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t b
      ((negativeKernelEquiv D Sc cutoff i v t hh).symm y) := by
  rw [moduleCapMatrixIso_inv_kernel, LinearEquiv.symm_apply_apply,
    BalancedKernelTensor.equivOfBijective_symm_tensor, indResKernelCoordinates_tensor]
  rfl

/-- The raw upper-Hom insertion selects precisely the principal negative inverse. -/
theorem moduleCapMatrixIso_principal_inv_tensor
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (v : OldCategory D Sc cutoff)
    (y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) (b : M.obj v) :
    (moduleCapMatrixIso D Sc cutoff M i t hh).inv
      (negativeKernelCoordinates D Sc cutoff M i _ t
        (BalancedKernelTensor.tensor _ M.toFunctor v (Pi.single none y) b)) =
    IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t b
      (negativeKernelPrincipalInverse D Sc cutoff i v t hh y) := by
  rw [moduleCapMatrixIso_inv_tensor]
  rfl

end CyclotomicCrossingTensor.TensorMatrixCoordinates
end OddMath.QuiverHecke.ELVOld
