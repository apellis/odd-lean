/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedIndResKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform

/-! # Ordinary-right kernels of two-functor crossing mates

The literal kernel map in `DeformedActionAssembly.md` §4 for
Brundan–Ellis (1.12). Crossing supernaturality proves lower balance;
ordinary right precomposition is retained without a representing sign.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld.MixedIndResKernel
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
variable (A B : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  [B.Additive] [B.Linear k] [IsSuperfunctor k B]
variable {p : ZMod 2} {α : ∀ s, (B ⋙ A).obj s ⟶ (A ⋙ B).obj s}
  (hα : IsSupernatural k p α)

private def matePair (v s t : C) : (A.obj s ⟶ t) →ₗ[k]
    (v ⟶ B.obj s) →ₗ[k] (A.obj v ⟶ B.obj t) where
  toFun g := Linear.rightComp k _ (α s ≫ twist k p (B.map g)) ∘ₗ A.mapLinearMap (R := k)
  map_add' g g' := by
    ext b
    simp only [LinearMap.comp_apply, Linear.rightComp_apply,
      Functor.map_add, map_add, Preadditive.comp_add, LinearMap.add_apply]
  map_smul' a g := by
    ext b
    simp only [LinearMap.comp_apply, Linear.rightComp_apply,
      Functor.map_smul, map_smul, Linear.comp_smul, LinearMap.smul_apply, RingHom.id_apply]

include hα in
private theorem matePair_balance (v s s' t : C) (f : s ⟶ s')
    (g : A.obj s' ⟶ t) (b : v ⟶ B.obj s) :
    matePair (k := k) A B (p := p) (α := α) v s t (A.map f ≫ g) b =
      matePair (k := k) A B (p := p) (α := α) v s' t g (b ≫ B.map f) := by
  have h := hα.naturality_twist f
  change A.map (B.map f) ≫ α s' = α s ≫ B.map (A.map (twist k p f)) at h
  rw [map_twist A, map_twist B] at h
  change A.map b ≫ α s ≫ twist k p (B.map (A.map f ≫ g)) =
    A.map (b ≫ B.map f) ≫ α s' ≫ twist k p (B.map g)
  calc
    _ = A.map b ≫ (α s ≫ twist k p (B.map (A.map f))) ≫ twist k p (B.map g) := by
      rw [Functor.map_comp, twist_comp]
      simp only [Category.assoc]
    _ = A.map b ≫ (A.map (B.map f) ≫ α s') ≫ twist k p (B.map g) :=
      congrArg (fun a : A.obj (B.obj s) ⟶ B.obj (A.obj s') =>
        A.map b ≫ a ≫ twist k p (B.map g)) h.symm
    _ = _ := by rw [Functor.map_comp]; simp only [Category.assoc]

/-- The ordered crossing-mate formula on the ordinary-right source kernel. -/
def mateComponent (v t : C) : Component (k := k) A B v t →ₗ[k] (A.obj v ⟶ B.obj t) :=
  BalancedInduction.lift A (B ⋙ IndResKernel.homModule (k := k) v) t
    (fun s => TensorProduct.lift (matePair (k := k) A B (p := p) (α := α) v s t))
    (fun s s' f g b => matePair_balance A B hα v s s' t f g b)

@[simp] theorem mateComponent_tensor (v s t : C) (g : A.obj s ⟶ t) (b : v ⟶ B.obj s) :
    mateComponent A B hα v t
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b) =
      A.map b ≫ α s ≫ twist k p (B.map g) := by
  rw [mateComponent, BalancedInduction.lift_tensor]
  rfl

theorem mateComponent_precompose (u v t : C) (r : u ⟶ v) :
    mateComponent A B hα u t ∘ₗ precompose (k := k) A B r t =
      (Linear.leftComp k _ (A.map r)) ∘ₗ mateComponent A B hα v t := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, precompose_tensor, mateComponent_tensor,
    Linear.leftComp_apply, Functor.map_comp, Category.assoc]

end OddMath.QuiverHecke.ELVOld.MixedIndResKernel
