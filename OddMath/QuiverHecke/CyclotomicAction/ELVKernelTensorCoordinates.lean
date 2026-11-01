import OddMath.QuiverHecke.CyclotomicAction.ELVActualKernelMatrices
import OddMath.QuiverHecke.CyclotomicAction.ELVFiniteMatrixComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVQuotientInduction

/-! # Kernel tensor coordinates for the prescribed finite matrices

The underlying endpoint comparisons in DeformedMatrixComparison, section 4.
The many-object kernel quotients are identified with the existing induction,
restriction and finite shifted module families. Every shift uses its named
canonical parity isomorphism. No preservation of general categorical colimits
or flatness is assumed. Matrix-entry identification is a separate statement.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

local instance matrixCoordinatePi :
    PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

variable (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))

/-- Evaluation of the identity induction quotient, with identity insertion inverse. -/
def identityInductionCoordinates (t : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (𝟭 (OldCategory D Sc cutoff)) M.toFunctor t ≃ₗ[k] M.obj t :=
  LinearEquiv.ofLinearMap
    (BalancedInduction.counit (𝟭 _) M.toFunctor t)
    (BalancedInduction.unit (𝟭 _) M.toFunctor t)
    (BalancedInduction.counit_unit (𝟭 _) M.toFunctor t)
    (BalancedInduction.unit_counit_of_full (𝟭 _) M.toFunctor t)

/-- The identity-Hom coefficient kernel evaluates on an arbitrary module. -/
def identityKernelCoordinates (t : OldCategory D Sc cutoff) :
    BalancedKernelTensor.Obj (BalancedKernelTensor.inductionKernel (k := k)
      (𝟭 (OldCategory D Sc cutoff)) t) M.toFunctor ≃ₗ[k] M.obj t :=
  (BalancedKernelTensor.inductionKernelEquiv (𝟭 _) M.toFunctor t).trans
    (identityInductionCoordinates D Sc cutoff M t)

@[simp] theorem identityKernelCoordinates_tensor (v t : OldCategory D Sc cutoff)
    (b : v ⟶ t) (m : M.obj v) :
    identityKernelCoordinates D Sc cutoff M t
      (BalancedKernelTensor.tensor (BalancedKernelTensor.inductionKernel (k := k)
        (𝟭 (OldCategory D Sc cutoff)) t) M.toFunctor v b m) = M.map b m := by
  change BalancedInduction.counit (𝟭 _) M.toFunctor t
    (BalancedInduction.tensor (𝟭 _) M.toFunctor v b m) = _
  exact BalancedInduction.counit_tensor (𝟭 _) M.toFunctor t v b m

/-- The IndRes coefficient tensor is the literal source of the cap matrix. -/
def indResKernelCoordinates (i : I) (t : OldCategory D Sc cutoff) :
    BalancedKernelTensor.Obj (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
      M.toFunctor ≃ₗ[k]
      ((BalancedInduction.induction (append D Sc cutoff i)).obj
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t :=
  IndResKernel.equiv (append D Sc cutoff i) M.toFunctor t

/-- The upper Hom coefficient tensor is the literal target of the unit matrix. -/
def resIndKernelCoordinates (i : I) (t : OldCategory D Sc cutoff) :
    BalancedKernelTensor.Obj (BalancedKernelTensor.inductionKernel (k := k)
      (append D Sc cutoff i) ((append D Sc cutoff i).obj t)) M.toFunctor ≃ₗ[k]
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M)).obj t :=
  BalancedKernelTensor.inductionKernelEquiv (append D Sc cutoff i) M.toFunctor
    ((append D Sc cutoff i).obj t)

/-- Each unit-source slot uses exactly the canonical source parity coordinate. -/
def positiveSlotCoordinates (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (a : Option (Fin m)) :
    BalancedKernelTensor.Obj (positiveKernelFamily D Sc cutoff i m t a) M.toFunctor ≃ₗ[k]
      (unitMatrixFamily D Sc cutoff i M m a).obj t :=
  match a with
  | none => (indResKernelCoordinates D Sc cutoff M i t).trans
      (moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M m) t).symm
  | some r => (identityKernelCoordinates D Sc cutoff M t).trans
      (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
        (r.val • D.parity i)).iso M) t).symm

/-- Each cap-target slot uses exactly the canonical target parity coordinate. -/
def negativeSlotCoordinates (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (a : Option (Fin m)) :
    BalancedKernelTensor.Obj (negativeKernelFamily D Sc cutoff i m t a) M.toFunctor ≃ₗ[k]
      (capMatrixFamily D Sc cutoff i M m a).obj t :=
  match a with
  | none => (resIndKernelCoordinates D Sc cutoff M i t).trans
      (moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t).symm
  | some r => (identityKernelCoordinates D Sc cutoff M t).trans
      (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
        (r.val • D.parity i)).iso M) t).symm

/-- The finite source coend realizes the exact shifted unit-matrix source. -/
def positiveKernelCoordinates (i : I) (m : ℕ) (t : OldCategory D Sc cutoff) :
    BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t))
        M.toFunctor ≃ₗ[k] unitMatrixSourceSpace D Sc cutoff i M m t :=
  (BalancedKernelTensor.piEquiv (positiveKernelFamily D Sc cutoff i m t) M.toFunctor).trans
    (LinearEquiv.piCongrRight (positiveSlotCoordinates D Sc cutoff M i m t))

/-- The finite target coend realizes the exact shifted cap-matrix target. -/
def negativeKernelCoordinates (i : I) (m : ℕ) (t : OldCategory D Sc cutoff) :
    BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff i m t))
        M.toFunctor ≃ₗ[k] capMatrixTargetSpace D Sc cutoff i M m t :=
  (BalancedKernelTensor.piEquiv (negativeKernelFamily D Sc cutoff i m t) M.toFunctor).trans
    (LinearEquiv.piCongrRight (negativeSlotCoordinates D Sc cutoff M i m t))

theorem positiveKernelCoordinates_apply (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (z : BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)) M.toFunctor)
    (a : Option (Fin m)) :
    positiveKernelCoordinates D Sc cutoff M i m t z a =
      positiveSlotCoordinates D Sc cutoff M i m t a
        (BalancedKernelTensor.map M.toFunctor
          (BalancedKernelTensor.piProjection (positiveKernelFamily D Sc cutoff i m t) a) z) := rfl

theorem negativeKernelCoordinates_apply (i : I) (m : ℕ) (t : OldCategory D Sc cutoff)
    (z : BalancedKernelTensor.Obj
      (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff i m t)) M.toFunctor)
    (a : Option (Fin m)) :
    negativeKernelCoordinates D Sc cutoff M i m t z a =
      negativeSlotCoordinates D Sc cutoff M i m t a
        (BalancedKernelTensor.map M.toFunctor
          (BalancedKernelTensor.piProjection (negativeKernelFamily D Sc cutoff i m t) a) z) := rfl

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.TensorMatrixCoordinates
