/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctMateKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedMateLinear

/-! # The prescribed distinct mate on arbitrary old modules

Brundan–Ellis (1.12), `DeformedActionAssembly.md` §4: tensor the ordinary-right
coefficient kernel isomorphism with the entire input module. The explicit
coend comparison identifies the resulting map with the fixed rectangular
cup-crossing-cap. No flatness or projectivity is required.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The fixed categorical mate with source and target coends exposed. -/
def moduleMateLinear (i j : I) (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (append D Sc cutoff i) ((append D Sc cutoff j) ⋙ N.toFunctor) t →ₗ[k]
      BalancedInduction.Obj (append D Sc cutoff i) N.toFunctor ((append D Sc cutoff j).obj t) :=
  BalancedInduction.orderedMixedMateCoend (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) N t

@[simp] theorem moduleMateLinear_tensor (i j : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : N.obj ((append D Sc cutoff j).obj s)) :
    moduleMateLinear D Sc cutoff i j N t
      (BalancedInduction.tensor (append D Sc cutoff i) ((append D Sc cutoff j) ⋙ N.toFunctor) s g b) =
      BalancedInduction.tensor (append D Sc cutoff i) N.toFunctor ((append D Sc cutoff j).obj s)
        (crossComponent D Sc cutoff i j s ≫
          twist k (D.parity i * D.parity j) ((append D Sc cutoff j).map g)) b :=
  BalancedInduction.orderedMixedMateCoend_tensor (append D Sc cutoff i) (append D Sc cutoff j)
    (cross_supernatural D Sc cutoff i j) N s t g b

private theorem moduleMate_evaluate (i j : I)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (v t : OldCategory D Sc cutoff)
    (m : N.obj v) :
    moduleMateLinear D Sc cutoff i j N t ∘ₗ
      MixedIndResKernel.evaluate (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor v t m =
      BalancedInduction.inclusion (append D Sc cutoff i) N.toFunctor ((append D Sc cutoff j).obj t) v ∘ₗ
        (TensorProduct.mk k _ _).flip m ∘ₗ kernelMateComponent D Sc cutoff i j v t := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, MixedIndResKernel.evaluate_tensor,
    moduleMateLinear_tensor, kernelMateComponent_tensor, LinearMap.flip_apply,
    TensorProduct.mk_apply]
  change BalancedInduction.tensor (append D Sc cutoff i) N.toFunctor
      ((append D Sc cutoff j).obj s) _ (N.map b m) =
    BalancedInduction.tensor (append D Sc cutoff i) N.toFunctor v _ m
  exact (BalancedInduction.balance (append D Sc cutoff i) N.toFunctor b
    (crossComponent D Sc cutoff i j s ≫
      twist k (D.parity i * D.parity j) ((append D Sc cutoff j).map g)) m).symm

/-- Tensor the constructed ordinary-right kernel inverse with any old module. -/
def moduleMateUnderlyingEquiv (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (append D Sc cutoff i) ((append D Sc cutoff j) ⋙ N.toFunctor) t ≃ₗ[k]
      BalancedInduction.Obj (append D Sc cutoff i) N.toFunctor ((append D Sc cutoff j).obj t) :=
  (MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t).symm |>.trans
    ((BalancedKernelTensor.equiv N.toFunctor (kernelMateIso D Sc cutoff i j hij t)).trans
      (BalancedKernelTensor.inductionKernelEquiv (append D Sc cutoff i) N.toFunctor
        ((append D Sc cutoff j).obj t)))

private theorem moduleMateUnderlyingEquiv_forward_tensor (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (v t : OldCategory D Sc cutoff)
    (x : MixedIndResKernel.Component (k := k) (append D Sc cutoff i) (append D Sc cutoff j) v t)
    (m : N.obj v) :
    moduleMateUnderlyingEquiv D Sc cutoff i j hij N t
      (MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t
        (BalancedKernelTensor.tensor (MixedIndResKernel.kernel (k := k) (append D Sc cutoff i) (append D Sc cutoff j) t) N.toFunctor v x m)) =
      BalancedInduction.tensor (append D Sc cutoff i) N.toFunctor v
        (kernelMateComponent D Sc cutoff i j v t x) m := by
  change ((MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t).symm.trans
    ((BalancedKernelTensor.equiv N.toFunctor (kernelMateIso D Sc cutoff i j hij t)).trans
      (BalancedKernelTensor.inductionKernelEquiv (append D Sc cutoff i) N.toFunctor
        ((append D Sc cutoff j).obj t))))
    ((MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t)
      (BalancedKernelTensor.tensor (MixedIndResKernel.kernel (k := k) (append D Sc cutoff i) (append D Sc cutoff j) t) N.toFunctor v x m)) = _
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply,
    BalancedKernelTensor.equiv_tensor, BalancedKernelTensor.inductionKernelEquiv_tensor]
  rfl

private theorem equiv_eq_on_kernel_tensors
    {C : Type u} [Category.{u} C] (K : Cᵒᵖ ⥤ ModuleCat k) (M : C ⥤ SVec k)
    {V W : Type u} [AddCommMonoid V] [Module k V] [AddCommGroup W] [Module k W]
    (e : V ≃ₗ[k] W) (f : V →ₗ[k] W) (q : BalancedKernelTensor.Obj K M ≃ₗ[k] V)
    (h : ∀ v (x : K.obj (op v)) (m : M.obj v),
      e (q (BalancedKernelTensor.tensor K M v x m)) =
        f (q (BalancedKernelTensor.tensor K M v x m))) : e.toLinearMap = f := by
  apply LinearMap.cancel_right q.surjective |>.mp
  apply BalancedKernelTensor.hom_ext
  intro v x m
  exact h v x m

private theorem coend_left_apply
    {C B : Type u} [Category.{u} C] [Category.{u} B] [Preadditive B] [Linear k B]
    (J : C ⥤ B) (M : C ⥤ SVec k) (w : B) (v : C)
    {V : Type u} [AddCommMonoid V] [Module k V] (L : V →ₗ[k] (J.obj v ⟶ w))
    (m : M.obj v) (x : V) :
    (BalancedInduction.inclusion J M w v ∘ₗ (TensorProduct.mk k _ _).flip m ∘ₗ L) x =
      BalancedInduction.tensor J M v (L x) m := rfl

/-- The quotient-level inverse has exactly the prescribed categorical forward map. -/
theorem moduleMateUnderlyingEquiv_toLinearMap (i j : I) (hij : i ≠ j)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff) :
    (moduleMateUnderlyingEquiv D Sc cutoff i j hij N t).toLinearMap =
      moduleMateLinear D Sc cutoff i j N t := by
  apply equiv_eq_on_kernel_tensors (k := k)
    (MixedIndResKernel.kernel (k := k) (append D Sc cutoff i) (append D Sc cutoff j) t) N.toFunctor
    (moduleMateUnderlyingEquiv D Sc cutoff i j hij N t) (moduleMateLinear D Sc cutoff i j N t)
    (MixedIndResKernel.equiv (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t)
  intro v x m
  have hL := moduleMateUnderlyingEquiv_forward_tensor D Sc cutoff i j hij N v t x m
  have hF := congrArg (moduleMateLinear D Sc cutoff i j N t)
    (MixedIndResKernel.equiv_tensor (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor t v x m)
  have hA := LinearMap.congr_fun (moduleMate_evaluate D Sc cutoff i j N v t m) x
  have hA0 := (LinearMap.comp_apply (moduleMateLinear D Sc cutoff i j N t)
    (MixedIndResKernel.evaluate (append D Sc cutoff i) (append D Sc cutoff j) N.toFunctor v t m) x).symm.trans hA
  have hA1 := hA0.trans (coend_left_apply (k := k) (append D Sc cutoff i) N.toFunctor
    ((append D Sc cutoff j).obj t) v (kernelMateComponent D Sc cutoff i j v t) m x)
  exact hL.trans (hF.trans hA1).symm

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
