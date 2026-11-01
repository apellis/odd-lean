import OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernel

/-! # Target naturality of the induction-restriction kernel

The target action and compatibility of the explicit kernel realization in
DeformedMatrixComparison, section 4. All maps use the existing balanced
quotients. This is ordinary underlying naturality; grading transport is a
separate statement.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.IndResKernel
universe u
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D] [Supercategory k D]
variable (J : C ⥤ D)

/-- Postcomposition on the outer induction arrow commutes with source balance. -/
def targetMap {t t' : D} (a : t ⟶ t') :
    kernel (k := k) J t ⟶ kernel (k := k) J t' where
  app v := ModuleCat.ofHom
    (BalancedInduction.postcompose J (J ⋙ homModule (k := k) v.unop) a)
  naturality v w f := by
    apply ModuleCat.hom_ext
    apply BalancedInduction.hom_ext
    intro s g b
    change BalancedInduction.postcompose J (J ⋙ homModule (k := k) w.unop) a
        (precompose (k := k) J f.unop t
          (BalancedInduction.tensor J (J ⋙ homModule (k := k) v.unop) s g b)) =
      precompose (k := k) J f.unop t'
        (BalancedInduction.postcompose J (J ⋙ homModule (k := k) v.unop) a
          (BalancedInduction.tensor J (J ⋙ homModule (k := k) v.unop) s g b))
    simp only [precompose_tensor, BalancedInduction.postcompose_tensor]

@[simp] theorem targetMap_app {t t' : D} (a : t ⟶ t') (v : D)
    (x : Component (k := k) J v t) :
    (targetMap (k := k) J a).app (op v) x =
      BalancedInduction.postcompose J (J ⋙ homModule (k := k) v) a x := rfl

/-- The coefficient kernel is covariant in the ambient target. -/
def kernelFunctor : D ⥤ (Dᵒᵖ ⥤ ModuleCat k) where
  obj := kernel (k := k) J
  map := targetMap (k := k) J
  map_id t := by
    apply NatTrans.ext
    funext v
    apply ModuleCat.hom_ext
    exact BalancedInduction.postcompose_id J (J ⋙ homModule (k := k) v.unop) t
  map_comp a b := by
    apply NatTrans.ext
    funext v
    apply ModuleCat.hom_ext
    exact BalancedInduction.postcompose_comp J (J ⋙ homModule (k := k) v.unop) a b

variable (M : D ⥤ SVec k) [M.Additive] [M.Linear k]

theorem evaluate_postcompose {t t' : D} (a : t ⟶ t') (v : D) (m : M.obj v) :
    evaluate J M v t' m ∘ₗ
        BalancedInduction.postcompose J (J ⋙ homModule (k := k) v) a =
      BalancedInduction.postcompose J (J ⋙ M) a ∘ₗ evaluate J M v t m := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, BalancedInduction.postcompose_tensor, evaluate_tensor]

/-- The kernel tensor realization intertwines every target morphism. -/
theorem forward_targetMap {t t' : D} (a : t ⟶ t') :
    forward J M t' ∘ₗ BalancedKernelTensor.map M (targetMap (k := k) J a) =
      BalancedInduction.postcompose J (J ⋙ M) a ∘ₗ forward J M t := by
  apply BalancedKernelTensor.hom_ext
  intro v x m
  simp only [LinearMap.comp_apply, BalancedKernelTensor.map_tensor, forward_tensor,
    targetMap_app]
  exact congrArg (fun f => f x) (evaluate_postcompose J M a v m)

omit [M.Additive] [M.Linear k] in
/-- Inverse target naturality follows from the checked quotient roundtrips. -/
theorem backward_postcompose {t t' : D} (a : t ⟶ t') :
    backward J M t' ∘ₗ BalancedInduction.postcompose J (J ⋙ M) a =
      BalancedKernelTensor.map M (targetMap (k := k) J a) ∘ₗ backward J M t := by
  apply BalancedInduction.hom_ext
  intro s g m
  simp only [LinearMap.comp_apply, BalancedInduction.postcompose_tensor,
    backward_tensor, BalancedKernelTensor.map_tensor, targetMap_app, identityLift_apply]

omit [M.Additive] [M.Linear k] in
/-- Target action on the coefficient tensor quotients, before grading. -/
def tensorFunctor : D ⥤ ModuleCat k where
  obj t := ModuleCat.of k (BalancedKernelTensor.Obj (kernel (k := k) J t) M)
  map a := ModuleCat.ofHom (BalancedKernelTensor.map M (targetMap (k := k) J a))
  map_id t := by
    apply ModuleCat.hom_ext
    apply BalancedKernelTensor.hom_ext
    intro v x m
    change BalancedKernelTensor.map M (targetMap (k := k) J (𝟙 t))
      (BalancedKernelTensor.tensor (kernel (k := k) J t) M v x m) =
      BalancedKernelTensor.tensor (kernel (k := k) J t) M v x m
    simp only [BalancedKernelTensor.map_tensor, targetMap_app,
      BalancedInduction.postcompose_id, LinearMap.id_apply]
  map_comp a b := by
    apply ModuleCat.hom_ext
    apply BalancedKernelTensor.hom_ext
    intro v x m
    change BalancedKernelTensor.map M (targetMap (k := k) J (a ≫ b))
      (BalancedKernelTensor.tensor (kernel (k := k) J _) M v x m) =
      BalancedKernelTensor.map M (targetMap (k := k) J b)
        (BalancedKernelTensor.map M (targetMap (k := k) J a)
          (BalancedKernelTensor.tensor (kernel (k := k) J _) M v x m))
    simp only [BalancedKernelTensor.map_tensor, targetMap_app,
      BalancedInduction.postcompose_comp, LinearMap.comp_apply]

end OddMath.QuiverHecke.ELVOld.IndResKernel
