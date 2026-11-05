/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionMixedMateTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionCoefficientIso

/-! # Fixed-endpoint linear maps of two-functor mates

The coend-level forward map needed in the arbitrary-module proof of
Brundan–Ellis (1.12), `DeformedActionAssembly.md` §4. The endpoints are fixed
before specializing to the old ELV category.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
variable (A B : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  [B.Additive] [B.Linear k] [IsSuperfunctor k B]
variable {p : ZMod 2} {α : ∀ s, (B ⋙ A).obj s ⟶ (A ⋙ B).obj s}
  (hα : IsSupernatural k p α)

private def restrictionCoefficientIso (N : Superfunctor k C (SVec k)) :
    B ⋙ N.toFunctor ≅ ((restriction B).obj N).toFunctor := Iso.refl _

private def restrictionSourceEquiv (N : Superfunctor k C (SVec k)) (t : C) :
    Obj A (B ⋙ N.toFunctor) t ≃ₗ[k] (induced A ((restriction B).obj N)).obj t :=
  coefficientEquiv A (restrictionCoefficientIso B N) t

private theorem restrictionSourceEquiv_toLinearMap (N : Superfunctor k C (SVec k)) (t : C) :
    (restrictionSourceEquiv A B N t).toLinearMap = LinearMap.id :=
  coefficientMap_id A t

def orderedMixedMateLinear (N : Superfunctor k C (SVec k)) (t : C) :
    (induced A ((restriction B).obj N)).obj t →ₗ[k] ((restriction B).obj (induced A N)).obj t :=
  (orderedMixedMateComponent (k := k) A B hα N).total t

@[simp] theorem orderedMixedMateLinear_tensor (N : Superfunctor k C (SVec k))
    (s t : C) (g : A.obj s ⟶ t) (b : N.obj (B.obj s)) :
    orderedMixedMateLinear (k := k) A B hα N t
      (tensor A ((restriction B).obj N).toFunctor s g b) =
      tensor A N.toFunctor (B.obj s) (α s ≫ twist k p (B.map g)) b :=
  orderedMixedMateComponent_total_tensor (k := k) A B hα N s t g b

/-- The ordinary coend coordinates are compared before applying the categorical mate. -/
def orderedMixedMateCoend (N : Superfunctor k C (SVec k)) (t : C) :
    Obj A (B ⋙ N.toFunctor) t →ₗ[k] Obj A N.toFunctor (B.obj t) :=
  orderedMixedMateLinear (k := k) A B hα N t ∘ₗ (restrictionSourceEquiv A B N t).toLinearMap

theorem orderedMixedMateCoend_eq_linear (N : Superfunctor k C (SVec k)) (t : C) :
    orderedMixedMateCoend (k := k) A B hα N t = orderedMixedMateLinear (k := k) A B hα N t := by
  rw [orderedMixedMateCoend, restrictionSourceEquiv_toLinearMap, LinearMap.comp_id]

@[simp] theorem orderedMixedMateCoend_tensor (N : Superfunctor k C (SVec k))
    (s t : C) (g : A.obj s ⟶ t) (b : N.obj (B.obj s)) :
    orderedMixedMateCoend (k := k) A B hα N t (tensor A (B ⋙ N.toFunctor) s g b) =
      tensor A N.toFunctor (B.obj s) (α s ≫ twist k p (B.map g)) b := by
  have he := congrArg (fun f : Obj A (B ⋙ N.toFunctor) t →ₗ[k] Obj A N.toFunctor (B.obj t) =>
    f (tensor A (B ⋙ N.toFunctor) s g b)) (orderedMixedMateCoend_eq_linear (k := k) A B hα N t)
  have hs : tensor A (B ⋙ N.toFunctor) s g b = tensor A ((restriction B).obj N).toFunctor s g b := rfl
  have ht := orderedMixedMateLinear_tensor (k := k) A B hα N s t g b
  exact he.trans ((congrArg (orderedMixedMateLinear (k := k) A B hα N t) hs).trans ht)

end OddMath.QuiverHecke.ELVOld.BalancedInduction
