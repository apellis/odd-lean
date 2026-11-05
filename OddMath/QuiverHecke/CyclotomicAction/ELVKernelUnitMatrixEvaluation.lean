import OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixEvaluation

/-! # Kernel realization of the whole unit-column matrix

The positive-profile arbitrary-module transfer in DeformedMatrixComparison §4,
with the prescribed unscaled unit columns and canonical source parity coordinates.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
