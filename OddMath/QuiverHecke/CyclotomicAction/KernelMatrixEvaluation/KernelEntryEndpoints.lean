import OddMath.QuiverHecke.CyclotomicAction.KernelMatrixEvaluation.KernelEntryEvaluation
import OddMath.QuiverHecke.CyclotomicAction.KernelMatrixEvaluation.KernelMatrixBijective

/-!
# Kernel matrix evaluation

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Fixed module endpoints for mate-kernel evaluation

The mate comparison needed by DeformedMatrixComparison, section 4, with both
linear maps valued in the literal restriction-induction module. The existing
coefficient comparison is retained unchanged; its pointwise equality is used
to attach the common target module before applying the maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (i : I) (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))

abbrev mateSourceSpace (t : OldCategory D Sc cutoff) : SVec k :=
  ((BalancedInduction.induction (append D Sc cutoff i)).obj
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t

abbrev mateTargetSpace (t : OldCategory D Sc cutoff) : SVec k :=
  ((BalancedInduction.restriction (append D Sc cutoff i)).obj
    ((BalancedInduction.induction (append D Sc cutoff i)).obj M)).obj t

/-- The prescribed mate as a linear map with its two literal module endpoints. -/
def moduleMateLinear (t : OldCategory D Sc cutoff) :
    mateSourceSpace D Sc cutoff i M t →ₗ[k] mateTargetSpace D Sc cutoff i M t :=
  SVec.toLinearMap ((matrixMateComponent D Sc cutoff i M).total t)

/-- Coefficient evaluation with the same literal restriction-induction target. -/
def mateCoefficientEvaluation (v t : OldCategory D Sc cutoff) (m : M.obj v) :
    ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) →ₗ[k]
      mateTargetSpace D Sc cutoff i M t :=
  BalancedInduction.coefficientEvaluation (append D Sc cutoff i) M.toFunctor
    v ((append D Sc cutoff i).obj t) m

/-- Source coefficient evaluation with the literal mate-source dictionary. -/
def mateSourceEvaluation (v t : OldCategory D Sc cutoff) (m : M.obj v) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k]
      mateSourceSpace D Sc cutoff i M t :=
  moduleSourceEvaluation D Sc cutoff i M v t m

def kernelMateEvaluationEndpoint (v t : OldCategory D Sc cutoff) (m : M.obj v) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k]
      mateTargetSpace D Sc cutoff i M t :=
  (mateCoefficientEvaluation D Sc cutoff i M v t m).comp
    (mateKernelComponent D Sc cutoff i v t)

def moduleMateEvaluationEndpoint (v t : OldCategory D Sc cutoff) (m : M.obj v) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k]
      mateTargetSpace D Sc cutoff i M t :=
  (moduleMateLinear D Sc cutoff i M t).comp
    (mateSourceEvaluation D Sc cutoff i M v t m)

@[simp] theorem kernelMateEvaluationEndpoint_apply (v t : OldCategory D Sc cutoff)
    (m : M.obj v) (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    kernelMateEvaluationEndpoint D Sc cutoff i M v t m z =
      mateCoefficientEvaluation D Sc cutoff i M v t m
        (mateKernelComponent D Sc cutoff i v t z) := rfl

@[simp] theorem moduleMateEvaluationEndpoint_apply (v t : OldCategory D Sc cutoff)
    (m : M.obj v) (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    moduleMateEvaluationEndpoint D Sc cutoff i M v t m z =
      moduleMateLinear D Sc cutoff i M t
        (mateSourceEvaluation D Sc cutoff i M v t m z) := rfl

@[simp] theorem mateCoefficientEvaluation_apply (v t : OldCategory D Sc cutoff)
    (m : M.obj v)
    (f : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) :
    mateCoefficientEvaluation D Sc cutoff i M v t m f =
      BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v f m := rfl

/-- Total evaluation is exposed only after both literal endpoints have been fixed. -/
theorem moduleMateLinear_apply (t : OldCategory D Sc cutoff)
    (z : mateSourceSpace D Sc cutoff i M t) :
    moduleMateLinear D Sc cutoff i M t z =
      (matrixMateComponent D Sc cutoff i M).total t z := rfl

@[simp] theorem mateSourceEvaluation_apply (v t : OldCategory D Sc cutoff)
    (m : M.obj v) (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    mateSourceEvaluation D Sc cutoff i M v t m z =
      moduleSourceEvaluation D Sc cutoff i M v t m z := rfl

theorem mateSourceEvaluation_tensor (v s t : OldCategory D Sc cutoff) (m : M.obj v)
    (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : v ⟶ (append D Sc cutoff i).obj s) :
    mateSourceEvaluation D Sc cutoff i M v t m
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) =
      BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M).toFunctor
          s g (M.map b m) :=
  IndResKernel.evaluate_tensor (append D Sc cutoff i) M.toFunctor v t m s g b

/-- The established mate coefficient equality, now between the matching module endpoints. -/
theorem mateEvaluationEndpoints_eq (v t : OldCategory D Sc cutoff) (m : M.obj v) :
    kernelMateEvaluationEndpoint D Sc cutoff i M v t m =
      moduleMateEvaluationEndpoint D Sc cutoff i M v t m := by
  apply BalancedInduction.hom_ext
  intro s g b
  rw [kernelMateEvaluationEndpoint_apply, moduleMateEvaluationEndpoint_apply,
    mateCoefficientEvaluation_apply, mateSourceEvaluation_tensor, moduleMateLinear_apply]
  exact mateKernel_evaluate_tensor D Sc cutoff i M v t m s g b

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Kernel realization of the whole categorical matrices

The arbitrary-module transfer in DeformedMatrixComparison §4 must identify
the entire forward map with the prescribed mate/unit/cap matrix.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.TensorMatrixCoordinates
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

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.TensorMatrixCoordinates
end

end

section

/-! # Kernel realization of the whole unit-column matrix

The positive-profile arbitrary-module transfer in DeformedMatrixComparison §4,
with the prescribed unscaled unit columns and canonical source parity coordinates.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
  (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)

local instance unitMatrixEvaluationPi :
    PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- The coefficient-kernel map with its literal module target. -/
def unitKernelForward :
    BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t))
        M.toFunctor →ₗ[k] mateTargetSpace D Sc cutoff i M t :=
  (resIndKernelCoordinates D Sc cutoff M i t).toLinearMap.comp
    (BalancedKernelTensor.map M.toFunctor (positiveKernelMap D Sc cutoff i m t))

/-- The actual unit matrix with its named source and target superspaces. -/
def unitMatrixLinear : unitMatrixSourceSpace D Sc cutoff i M m t →ₗ[k]
    mateTargetSpace D Sc cutoff i M t :=
  SVec.toLinearMap (unitMatrixComponent D Sc cutoff i M m t)

/-- Source coordinates with the same literal finite superspace dictionary. -/
def unitSourceCoordinatesLinear :
    BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor →ₗ[k]
      unitMatrixSourceSpace D Sc cutoff i M m t :=
  (positiveKernelCoordinates D Sc cutoff M i m t).toLinearMap

/-- The prescribed categorical unit matrix on the same finite kernel source. -/
def unitModuleForward :
    BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t))
        M.toFunctor →ₗ[k] mateTargetSpace D Sc cutoff i M t :=
  (unitMatrixLinear D Sc cutoff M i m t).comp
    (unitSourceCoordinatesLinear D Sc cutoff M i m t)

def unitColumnLinear (n : ℕ) : M.obj t →ₗ[k] mateTargetSpace D Sc cutoff i M t :=
  SVec.toLinearMap ((moduleUnitColumn D Sc cutoff i M n).total t)

theorem unitColumnLinear_apply (n : ℕ) (b : M.obj t) :
    unitColumnLinear D Sc cutoff M i t n b =
      (moduleUnitColumn D Sc cutoff i M n).total t b := rfl

theorem unitModuleForward_apply
    (z : BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor) :
    unitModuleForward D Sc cutoff M i m t z =
      unitMatrixLinear D Sc cutoff M i m t
        (unitSourceCoordinatesLinear D Sc cutoff M i m t z) := rfl

theorem unitMatrixLinear_apply (z : unitMatrixSourceSpace D Sc cutoff i M m t) :
    unitMatrixLinear D Sc cutoff M i m t z =
      unitMatrixComponent D Sc cutoff i M m t z := rfl

theorem positiveKernelCoordinates_linear_apply
    (z : BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor)
    (a : Option (Fin m)) :
    (positiveKernelCoordinates D Sc cutoff M i m t).toLinearMap z a =
      positiveSlotCoordinates D Sc cutoff M i m t a
        (BalancedKernelTensor.map M.toFunctor
          (BalancedKernelTensor.piProjection (positiveKernelFamily D Sc cutoff i m t) a) z) := by
  have h := congrFun (LinearEquiv.coe_toLinearMap
    (positiveKernelCoordinates D Sc cutoff M i m t)) z
  exact (congrArg (fun x : unitMatrixSourceSpace D Sc cutoff i M m t => x a) h).trans
    (positiveKernelCoordinates_apply D Sc cutoff M i m t z a)

theorem unitSourceCoordinatesLinear_slot
    (z : BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor)
    (a : Option (Fin m)) :
    unitSourceCoordinatesLinear D Sc cutoff M i m t z a =
      positiveSlotCoordinates D Sc cutoff M i m t a
        (BalancedKernelTensor.map M.toFunctor
          (BalancedKernelTensor.piProjection (positiveKernelFamily D Sc cutoff i m t) a) z) :=
  positiveKernelCoordinates_linear_apply D Sc cutoff M i m t z a

theorem unitMatrixComponent_apply (z : unitMatrixSourceSpace D Sc cutoff i M m t) :
    unitMatrixComponent D Sc cutoff i M m t z =
      (unitMatrixEntry D Sc cutoff i M m none).total t (z none) +
        ∑ r : Fin m, (unitMatrixEntry D Sc cutoff i M m (some r)).total t (z (some r)) := by
  have h := OddMath.FiniteSuperspace.assembleColumns_apply
    (fun a => (unitMatrixFamily D Sc cutoff i M m a).obj t)
    (mateTargetSpace D Sc cutoff i M t)
    (fun a => (unitMatrixEntry D Sc cutoff i M m a).total t) z
  exact h.trans (Fintype.sum_option _)

theorem unitSlotCoordinates_none
    (z : BalancedKernelTensor.Obj (positiveKernelFamily D Sc cutoff i m t none) M.toFunctor) :
    (unitMatrixEntry D Sc cutoff i M m none).total t
      (positiveSlotCoordinates D Sc cutoff M i m t none z) =
      moduleMateLinear D Sc cutoff i M t (indResKernelCoordinates D Sc cutoff M i t z) := by
  have h := unitMatrixEntry_none_apply D Sc cutoff i M m t
    (positiveSlotCoordinates D Sc cutoff M i m t none z)
  exact h.trans ((moduleMateLinear_apply D Sc cutoff i M t _).symm.trans
    (congrArg (moduleMateLinear D Sc cutoff i M t)
      (positiveSlotCoordinates_none D Sc cutoff M i m t z)))

theorem unitSlotCoordinates_some (r : Fin m)
    (z : BalancedKernelTensor.Obj (positiveKernelFamily D Sc cutoff i m t (some r)) M.toFunctor) :
    (unitMatrixEntry D Sc cutoff i M m (some r)).total t
      (positiveSlotCoordinates D Sc cutoff M i m t (some r) z) =
      unitColumnLinear D Sc cutoff M i t r.val (identityKernelCoordinates D Sc cutoff M t z) := by
  have h := unitMatrixEntry_some_total D Sc cutoff i M t m r
    (positiveSlotCoordinates D Sc cutoff M i m t (some r) z)
  exact h.trans ((unitColumnLinear_apply D Sc cutoff M i t r.val _).symm.trans
    (congrArg (unitColumnLinear D Sc cutoff M i t r.val)
      (positiveSlotCoordinates_some D Sc cutoff M i m t r z)))

theorem unitSourceCoordinatesLinear_tensor (v : OldCategory D Sc cutoff)
    (x : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj (op v))
    (b : M.obj v) (a : Option (Fin m)) :
    unitSourceCoordinatesLinear D Sc cutoff M i m t
      (BalancedKernelTensor.tensor (BalancedKernelTensor.piKernel
        (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor v x b) a =
      positiveSlotCoordinates D Sc cutoff M i m t a
        (BalancedKernelTensor.tensor (positiveKernelFamily D Sc cutoff i m t a)
          M.toFunctor v (x a) b) := by
  rw [unitSourceCoordinatesLinear_slot, BalancedKernelTensor.map_tensor]
  rfl

theorem unitSlotCoordinates_none_tensor (v : OldCategory D Sc cutoff)
    (x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) (b : M.obj v) :
    (unitMatrixEntry D Sc cutoff i M m none).total t
      (positiveSlotCoordinates D Sc cutoff M i m t none
        (BalancedKernelTensor.tensor (positiveKernelFamily D Sc cutoff i m t none)
          M.toFunctor v x b)) =
      moduleMateLinear D Sc cutoff i M t (mateSourceEvaluation D Sc cutoff i M v t b x) := by
  rw [unitSlotCoordinates_none]
  exact congrArg (moduleMateLinear D Sc cutoff i M t)
    (indResKernelCoordinates_tensor_moduleSource D Sc cutoff M i t v x b)

theorem unitSlotCoordinates_some_tensor (v : OldCategory D Sc cutoff) (r : Fin m)
    (h : v ⟶ t) (b : M.obj v) :
    (unitMatrixEntry D Sc cutoff i M m (some r)).total t
      (positiveSlotCoordinates D Sc cutoff M i m t (some r)
        (BalancedKernelTensor.tensor (positiveKernelFamily D Sc cutoff i m t (some r))
          M.toFunctor v h b)) =
      unitColumnLinear D Sc cutoff M i t r.val (M.map h b) := by
  rw [unitSlotCoordinates_some]
  exact congrArg (unitColumnLinear D Sc cutoff M i t r.val)
    (identityKernelCoordinates_tensor D Sc cutoff M v t h b)

theorem unitModuleForward_tensor (v : OldCategory D Sc cutoff)
    (x : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj (op v))
    (b : M.obj v) :
    unitModuleForward D Sc cutoff M i m t
      (BalancedKernelTensor.tensor (BalancedKernelTensor.piKernel
        (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor v x b) =
      moduleMateLinear D Sc cutoff i M t (mateSourceEvaluation D Sc cutoff i M v t b (x none)) +
        ∑ r : Fin m, unitColumnLinear D Sc cutoff M i t r.val (M.map (x (some r)) b) := by
  rw [unitModuleForward_apply, unitMatrixLinear_apply, unitMatrixComponent_apply]
  simp_rw [unitSourceCoordinatesLinear_tensor]
  rw [unitSlotCoordinates_none_tensor]
  exact congrArg (fun y => moduleMateLinear D Sc cutoff i M t
      (mateSourceEvaluation D Sc cutoff i M v t b (x none)) + y)
    (Finset.sum_congr rfl (fun r _ =>
      unitSlotCoordinates_some_tensor D Sc cutoff M i m t v r (x (some r)) b))

theorem unitKernelForward_tensor (v : OldCategory D Sc cutoff)
    (x : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj (op v))
    (b : M.obj v) :
    unitKernelForward D Sc cutoff M i m t
      (BalancedKernelTensor.tensor (BalancedKernelTensor.piKernel
        (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor v x b) =
      mateCoefficientEvaluation D Sc cutoff i M v t b
        (mateKernelComponent D Sc cutoff i v t (x none)) +
        ∑ r : Fin m, mateCoefficientEvaluation D Sc cutoff i M v t b
          (unitKernelComponent D Sc cutoff i r.val v t (x (some r))) := by
  change resIndKernelCoordinates D Sc cutoff M i t
    (BalancedKernelTensor.map M.toFunctor (positiveKernelMap D Sc cutoff i m t)
      (BalancedKernelTensor.tensor (BalancedKernelTensor.piKernel
        (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor v x b)) = _
  rw [BalancedKernelTensor.map_tensor]
  have h := (resIndKernelCoordinates_tensor D Sc cutoff M i v t
    ((positiveKernelMap D Sc cutoff i m t).app (op v) x) b).trans
      (mateCoefficientEvaluation_apply D Sc cutoff i M v t b _).symm
  refine h.trans ?_
  have hc := congrArg (mateCoefficientEvaluation D Sc cutoff i M v t b)
    (positiveKernelMap_apply D Sc cutoff i m v t x)
  refine hc.trans ?_
  rw [map_add, map_sum]

/-- The whole transported unit-column map is the actual categorical unit matrix. -/
theorem unitKernelForward_eq_moduleForward :
    unitKernelForward D Sc cutoff M i m t = unitModuleForward D Sc cutoff M i m t := by
  apply BalancedKernelTensor.hom_ext
  intro v x b
  rw [unitKernelForward_tensor, unitModuleForward_tensor]
  apply congrArg₂ (fun x y => x + y)
  · exact (kernelMateEvaluationEndpoint_apply D Sc cutoff i M v t b (x none)).symm.trans
      ((LinearMap.congr_fun (mateEvaluationEndpoints_eq D Sc cutoff i M v t b) (x none)).trans
        (moduleMateEvaluationEndpoint_apply D Sc cutoff i M v t b (x none)))
  · apply Finset.sum_congr rfl
    intro r _
    exact (mateCoefficientEvaluation_apply D Sc cutoff i M v t b _).trans
      ((unitKernel_evaluate D Sc cutoff i M v t b r.val (x (some r))).trans
        (unitColumnLinear_apply D Sc cutoff M i t r.val _).symm)

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.TensorMatrixCoordinates
end

end

section

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
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.TensorMatrixCoordinates
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
      Function.Bijective ((positiveKernelMap D Sc cutoff i m t).app (op v))) :
    unitMatrixSourceSpace D Sc cutoff i M m t ≃ₗ[k] mateTargetSpace D Sc cutoff i M t :=
  (positiveKernelCoordinates D Sc cutoff M i m t).symm.trans
    ((BalancedKernelTensor.equivOfBijective M.toFunctor
      (positiveKernelMap D Sc cutoff i m t)
      (opComponents (fun v => Function.Bijective
        ((positiveKernelMap D Sc cutoff i m t).app v)) hb)).trans
        (resIndKernelCoordinates D Sc cutoff M i t))

private def transportedCapEquiv (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (hb : ∀ v : OldCategory D Sc cutoff,
      Function.Bijective ((negativeKernelMap D Sc cutoff i m t).app (op v))) :
    mateSourceSpace D Sc cutoff i M t ≃ₗ[k] capMatrixTargetSpace D Sc cutoff i M m t :=
  (indResKernelCoordinates D Sc cutoff M i t).symm.trans
    ((BalancedKernelTensor.equivOfBijective M.toFunctor
      (negativeKernelMap D Sc cutoff i m t)
      (opComponents (fun v => Function.Bijective
        ((negativeKernelMap D Sc cutoff i m t).app v)) hb)).trans
        (negativeKernelCoordinates D Sc cutoff M i m t))

private theorem transportedUnitEquiv_apply (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (hb : ∀ v : OldCategory D Sc cutoff,
      Function.Bijective ((positiveKernelMap D Sc cutoff i m t).app (op v)))
    (x : unitMatrixSourceSpace D Sc cutoff i M m t) :
    transportedUnitEquiv D Sc cutoff M i m t hb x = unitMatrixComponent D Sc cutoff i M m t x := by
  change resIndKernelCoordinates D Sc cutoff M i t
      (BalancedKernelTensor.map M.toFunctor (positiveKernelMap D Sc cutoff i m t)
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
      Function.Bijective ((negativeKernelMap D Sc cutoff i m t).app (op v)))
    (x : mateSourceSpace D Sc cutoff i M t) :
    transportedCapEquiv D Sc cutoff M i m t hb x = capMatrixComponent D Sc cutoff i M m t x := by
  change negativeKernelCoordinates D Sc cutoff M i m t
      (BalancedKernelTensor.map M.toFunctor (negativeKernelMap D Sc cutoff i m t)
        ((indResKernelCoordinates D Sc cutoff M i t).symm x)) = _
  have h := LinearMap.congr_fun (capKernelForward_eq_moduleForward D Sc cutoff M i m t)
    ((indResKernelCoordinates D Sc cutoff M i t).symm x)
  change negativeKernelCoordinates D Sc cutoff M i m t
      (BalancedKernelTensor.map M.toFunctor (negativeKernelMap D Sc cutoff i m t)
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
      (positiveKernelMap_bijective D Sc cutoff i t hh))

theorem moduleUnitMatrixIso_hom (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) :
    (moduleUnitMatrixIso D Sc cutoff M i t hh).hom =
      unitMatrixComponent D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) t := by
  apply LinearMap.ext
  intro x
  exact transportedUnitEquiv_apply D Sc cutoff M i
    (contentUnitCount D cutoff i (t.word : Multiset I)) t
      (positiveKernelMap_bijective D Sc cutoff i t hh) x

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
      (negativeKernelMap_bijective D Sc cutoff i t hh))

theorem moduleCapMatrixIso_hom (i : I) (t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) :
    (moduleCapMatrixIso D Sc cutoff M i t hh).hom =
      capMatrixComponent D Sc cutoff i M
        (contentCapCount D cutoff i (t.word : Multiset I)) t := by
  apply LinearMap.ext
  intro x
  exact transportedCapEquiv_apply D Sc cutoff M i
    (contentCapCount D cutoff i (t.word : Multiset I)) t
      (negativeKernelMap_bijective D Sc cutoff i t hh) x

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.TensorMatrixCoordinates
end

end
