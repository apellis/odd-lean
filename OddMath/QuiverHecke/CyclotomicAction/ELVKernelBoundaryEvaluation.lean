import OddMath.QuiverHecke.CyclotomicAction.ELVKernelBoundaryDegrees
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInverseKernelCoordinates

/-! # Evaluation of finite inverse window contractions

SwappedHomInversion §4 (7): every finite OLD module inverse coordinate
acts by its raw balanced-kernel coefficient. Canonical parity charts are
retained. This is the OLD evaluation step, before weighted content transport.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))

local instance boundaryEvaluationPi :
    PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- Removing the finite source parity chart identifies every unit inverse row. -/
theorem moduleUnitMatrixIso_window_inv_tensor
    (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (j : Fin (contentUnitCount D cutoff i (t.word : Multiset I)))
    (y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) (b : M.obj v) :
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
      (j.val • D.parity i)).iso M) t
      (((moduleUnitMatrixIso D Sc cutoff M i t hh).inv
        (BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v y b)) (some j)) =
    M.map (positiveKernelWindowInverse D Sc cutoff i v t hh j y) b := by
  rw [moduleUnitMatrixIso_inv_tensor, positiveKernelCoordinates_apply,
    BalancedKernelTensor.map_tensor, positiveSlotCoordinates_some]
  exact identityKernelCoordinates_tensor D Sc cutoff M v t _ b

/-- Single insertion in any finite cap target slot retains the canonical parity chart. -/
theorem negativeKernelCoordinates_window_single_tensor
    (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) (j : Fin m)
    (y : v ⟶ t) (b : M.obj v) :
    TensorMatrixCoordinates.negativeKernelCoordinates D Sc cutoff M i m t
      (BalancedKernelTensor.tensor _ M.toFunctor v (Pi.single (some j) y) b) =
    Pi.single (some j)
      ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
        (j.val • D.parity i)).iso M) t).symm (M.map y b)) := by
  classical
  funext a
  rw [negativeKernelCoordinates_apply, BalancedKernelTensor.map_tensor]
  change negativeSlotCoordinates D Sc cutoff M i m t a
    (BalancedKernelTensor.tensor _ M.toFunctor v
      ((Pi.single (some j) y : ∀ c, (negativeKernelFamily D Sc cutoff i m t c).obj (op v)) a) b) = _
  by_cases ha : a = some j
  · subst a
    simp only [Pi.single_eq_same]
    apply (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
      (j.val • D.parity i)).iso M) t).injective
    rw [negativeSlotCoordinates_some, LinearEquiv.apply_symm_apply]
    exact identityKernelCoordinates_tensor D Sc cutoff M v t y b
  · simp only [Pi.single_eq_of_ne ha, BalancedKernelTensor.tensor_zero_left, map_zero]

/-- Every cap inverse column evaluates the corresponding raw finite inverse column. -/
theorem moduleCapMatrixIso_window_inv_tensor
    (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (j : Fin (contentCapCount D cutoff i (t.word : Multiset I)))
    (y : v ⟶ t) (b : M.obj v) :
    (moduleCapMatrixIso D Sc cutoff M i t hh).inv
      (Pi.single (some j)
        ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
          (j.val • D.parity i)).iso M) t).symm (M.map y b))) =
    IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t b
      (negativeKernelWindowInverse D Sc cutoff i v t hh j y) := by
  rw [← negativeKernelCoordinates_window_single_tensor,
    moduleCapMatrixIso_inv_tensor]
  rfl

/-- Positive raw boundary coefficients evaluate by the finite unit inverse row. -/
theorem positiveKernelBoundary_evaluate
    (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (j : Fin (contentUnitCount D cutoff i (t.word : Multiset I)))
    (r : ℕ) (y : v ⟶ t) (b : M.obj v) :
    M.map (positiveKernelBoundary D Sc cutoff i v t hh j r y) b =
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
      (j.val • D.parity i)).iso M) t
      (((moduleUnitMatrixIso D Sc cutoff M i t hh).inv
        ((moduleUnitColumn D Sc cutoff i M r).total t (M.map y b))) (some j)) := by
  rw [positiveKernelBoundary, LinearMap.comp_apply,
    ← moduleUnitMatrixIso_window_inv_tensor, unitKernel_evaluate]

/-- Negative raw boundary coefficients evaluate by finite cap inverse insertion and cap. -/
theorem negativeKernelBoundary_evaluate
    (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (r : ℕ) (j : Fin (contentCapCount D cutoff i (t.word : Multiset I)))
    (y : v ⟶ t) (b : M.obj v) :
    M.map (negativeKernelBoundary D Sc cutoff i v t hh r j y) b =
    (moduleCapRow D Sc cutoff i M r).total t
      ((moduleCapMatrixIso D Sc cutoff M i t hh).inv
        (Pi.single (some j)
          ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
            (j.val • D.parity i)).iso M) t).symm (M.map y b)))) := by
  rw [negativeKernelBoundary, LinearMap.comp_apply,
    capKernel_evaluate_moduleCapRow, ← moduleCapMatrixIso_window_inv_tensor]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
