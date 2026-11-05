import OddMath.QuiverHecke.CyclotomicAction.ELVKernelTensorCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelEntryEndpoints

/-! # Kernel realization of the whole categorical matrices

The arbitrary-module transfer in DeformedMatrixComparison §4 must identify
the entire forward map with the prescribed mate/unit/cap matrix.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
  (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)

local instance matrixEvaluationPi :
    PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- The finite kernel map transported into the literal cap target family. -/
def capKernelForward :
    BalancedKernelTensor.Obj (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
      M.toFunctor →ₗ[k] capMatrixTargetSpace D Sc cutoff i M m t :=
  (negativeKernelCoordinates D Sc cutoff M i m t).toLinearMap.comp
    (BalancedKernelTensor.map M.toFunctor (negativeKernelMap D Sc cutoff i m t))

/-- The prescribed categorical cap matrix on the same kernel quotient source. -/
def capModuleForward :
    BalancedKernelTensor.Obj (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
      M.toFunctor →ₗ[k] capMatrixTargetSpace D Sc cutoff i M m t :=
  (SVec.toLinearMap (capMatrixComponent D Sc cutoff i M m t)).comp
    (indResKernelCoordinates D Sc cutoff M i t).toLinearMap

theorem indResKernelCoordinates_tensor_moduleSource (v : OldCategory D Sc cutoff)
    (x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) (b : M.obj v) :
    indResKernelCoordinates D Sc cutoff M i t
      (BalancedKernelTensor.tensor (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
        M.toFunctor v x b) = mateSourceEvaluation D Sc cutoff i M v t b x :=
  indResKernelCoordinates_tensor D Sc cutoff M i v t x b

theorem capModuleForward_apply
    (z : BalancedKernelTensor.Obj (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
      M.toFunctor) (a : Option (Fin m)) :
    capModuleForward D Sc cutoff M i m t z a =
      capMatrixComponent D Sc cutoff i M m t
        (indResKernelCoordinates D Sc cutoff M i t z) a := rfl

theorem capMatrixComponent_apply
    (z : ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t)
    (a : Option (Fin m)) :
    capMatrixComponent D Sc cutoff i M m t z a =
      (capMatrixEntry D Sc cutoff i M m a).total t z := rfl

theorem capKernelForward_none_tensor (v : OldCategory D Sc cutoff)
    (x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) (b : M.obj v) :
    moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t
      (capKernelForward D Sc cutoff M i m t
        (BalancedKernelTensor.tensor (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
          M.toFunctor v x b) none) =
      mateCoefficientEvaluation D Sc cutoff i M v t b
        (mateKernelComponent D Sc cutoff i v t x) := by
  change moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t
    (negativeKernelCoordinates D Sc cutoff M i m t
      (BalancedKernelTensor.map M.toFunctor (negativeKernelMap D Sc cutoff i m t)
        (BalancedKernelTensor.tensor (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
          M.toFunctor v x b)) none) = _
  rw [BalancedKernelTensor.map_tensor, negativeKernelCoordinates_apply,
    BalancedKernelTensor.map_tensor, negativeSlotCoordinates_none]
  change resIndKernelCoordinates D Sc cutoff M i t
    (BalancedKernelTensor.tensor (BalancedKernelTensor.inductionKernel (k := k)
      (append D Sc cutoff i) ((append D Sc cutoff i).obj t)) M.toFunctor v
      ((negativeKernelMap D Sc cutoff i m t).app (op v) x none) b) = _
  have hc := negativeKernelMap_none D Sc cutoff i m v t x
  exact (congrArg (fun g => resIndKernelCoordinates D Sc cutoff M i t
    (BalancedKernelTensor.tensor (BalancedKernelTensor.inductionKernel (k := k)
      (append D Sc cutoff i) ((append D Sc cutoff i).obj t)) M.toFunctor v g b)) hc).trans
    ((resIndKernelCoordinates_tensor D Sc cutoff M i v t _ b).trans
      (mateCoefficientEvaluation_apply D Sc cutoff i M v t b _).symm)

theorem capModuleForward_none
    (z : BalancedKernelTensor.Obj (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
      M.toFunctor) :
    moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t
      (capModuleForward D Sc cutoff M i m t z none) =
      moduleMateLinear D Sc cutoff i M t
        (indResKernelCoordinates D Sc cutoff M i t z) := by
  exact (congrArg (moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t)
    (capModuleForward_apply D Sc cutoff M i m t z none)).trans
    ((congrArg (moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t)
      (capMatrixComponent_apply D Sc cutoff M i m t _ none)).trans
        ((capMatrixEntry_none_apply D Sc cutoff i M m t _).trans
          (moduleMateLinear_apply D Sc cutoff i M t _).symm))

theorem capKernelForward_some_tensor (v : OldCategory D Sc cutoff)
    (x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) (b : M.obj v)
    (r : Fin m) :
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t
      (capKernelForward D Sc cutoff M i m t
        (BalancedKernelTensor.tensor (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
          M.toFunctor v x b) (some r)) =
      M.map (capKernelComponent D Sc cutoff i r.val v t x) b := by
  change moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t
    (negativeKernelCoordinates D Sc cutoff M i m t
      (BalancedKernelTensor.map M.toFunctor (negativeKernelMap D Sc cutoff i m t)
        (BalancedKernelTensor.tensor (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
          M.toFunctor v x b)) (some r)) = _
  rw [BalancedKernelTensor.map_tensor, negativeKernelCoordinates_apply,
    BalancedKernelTensor.map_tensor, negativeSlotCoordinates_some]
  change identityKernelCoordinates D Sc cutoff M t
    (BalancedKernelTensor.tensor (BalancedKernelTensor.inductionKernel (k := k)
      (𝟭 (OldCategory D Sc cutoff)) t) M.toFunctor v
      ((negativeKernelMap D Sc cutoff i m t).app (op v) x (some r)) b) = _
  have hc := negativeKernelMap_some D Sc cutoff i m v t r x
  exact (congrArg (fun g => identityKernelCoordinates D Sc cutoff M t
    (BalancedKernelTensor.tensor (BalancedKernelTensor.inductionKernel (k := k)
      (𝟭 (OldCategory D Sc cutoff)) t) M.toFunctor v g b)) hc).trans
    (identityKernelCoordinates_tensor D Sc cutoff M v t _ b)

theorem capModuleForward_some
    (z : BalancedKernelTensor.Obj (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
      M.toFunctor) (r : Fin m) :
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t
      (capModuleForward D Sc cutoff M i m t z (some r)) =
      (moduleCapRow D Sc cutoff i M r.val).total t
        (indResKernelCoordinates D Sc cutoff M i t z) := by
  change moduleIsoLinearEquiv
    ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t
    ((capMatrixEntry D Sc cutoff i M m (some r)).total t
      (indResKernelCoordinates D Sc cutoff M i t z)) = _
  exact capMatrixEntry_some_total D Sc cutoff i M t m r _

/-- The whole transported cap matrix is the actual categorical cap matrix. -/
theorem capKernelForward_eq_moduleForward :
    capKernelForward D Sc cutoff M i m t = capModuleForward D Sc cutoff M i m t := by
  apply BalancedKernelTensor.hom_ext
  intro v x b
  change IndResKernel.Component (k := k) (append D Sc cutoff i) v t at x
  funext a
  cases a with
  | none =>
    apply (moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t).injective
    rw [capKernelForward_none_tensor, capModuleForward_none,
      indResKernelCoordinates_tensor_moduleSource]
    exact (kernelMateEvaluationEndpoint_apply D Sc cutoff i M v t b x).symm.trans
      ((LinearMap.congr_fun (mateEvaluationEndpoints_eq D Sc cutoff i M v t b) x).trans
        (moduleMateEvaluationEndpoint_apply D Sc cutoff i M v t b x))
  | some r =>
    apply (moduleIsoLinearEquiv
      ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M) t).injective
    rw [capKernelForward_some_tensor, capModuleForward_some, indResKernelCoordinates_tensor]
    exact capKernel_evaluate_moduleCapRow D Sc cutoff i M v t b r.val x

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
