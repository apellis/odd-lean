import OddMath.QuiverHecke.CyclotomicAction.ELVKernelEntryEvaluation

/-! # Fixed module endpoints for mate-kernel evaluation

The mate comparison needed by DeformedMatrixComparison, section 4, with both
linear maps valued in the literal restriction-induction module. The existing
coefficient comparison is retained unchanged; its pointwise equality is used
to attach the common target module before applying the maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
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

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
