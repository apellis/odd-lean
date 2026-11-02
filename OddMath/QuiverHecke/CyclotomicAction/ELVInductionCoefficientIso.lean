/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTensor

/-! # Coefficient isomorphisms on balanced induction

The ordinary coefficient comparison needed in the arbitrary-module step of
Brundan–Ellis (1.12), `DeformedActionAssembly.md` §4. Coefficients change
before any module induction map or supernatural representing map is formed.
-/
noncomputable section
open CategoryTheory StringDiagrams TensorProduct
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D] (J : C ⥤ D)
variable {M N P : C ⥤ SVec k}

/-- Change only the coefficient in each prescribed balanced summand. -/
def coefficientMap (f : M ⟶ N) (w : D) : Obj J M w →ₗ[k] Obj J N w :=
  lift J M w (fun v => inclusion J N w v ∘ₗ
    TensorProduct.map LinearMap.id (SVec.toLinearMap (f.app v))) (by
      intro v v' r g m
      change tensor J N v (J.map r ≫ g) (f.app v m) =
        tensor J N v' g (f.app v' (M.map r m))
      rw [balance]
      congr 1
      have h := congrArg (fun a : M.obj v ⟶ N.obj v' => a m) (f.naturality r)
      exact h.symm)

@[simp] theorem coefficientMap_tensor (f : M ⟶ N) (w : D)
    (v : C) (g : J.obj v ⟶ w) (m : M.obj v) :
    coefficientMap J f w (tensor J M v g m) = tensor J N v g (f.app v m) := by
  rw [coefficientMap, lift_tensor]
  rfl

@[simp] theorem coefficientMap_id (w : D) : coefficientMap J (𝟙 M) w = LinearMap.id := by
  apply hom_ext
  intro v g m
  rw [coefficientMap_tensor]
  rfl

theorem coefficientMap_comp (f : M ⟶ N) (g : N ⟶ P) (w : D) :
    coefficientMap J (f ≫ g) w = coefficientMap J g w ∘ₗ coefficientMap J f w := by
  apply hom_ext
  intro v h m
  simp only [coefficientMap_tensor, LinearMap.comp_apply]
  rfl

/-- A coefficient natural isomorphism acts on the literal balanced quotient. -/
def coefficientEquiv (e : M ≅ N) (w : D) : Obj J M w ≃ₗ[k] Obj J N w :=
  LinearEquiv.ofLinearMap (coefficientMap J e.hom w) (coefficientMap J e.inv w)
    (by rw [← coefficientMap_comp, e.inv_hom_id, coefficientMap_id])
    (by rw [← coefficientMap_comp, e.hom_inv_id, coefficientMap_id])

@[simp] theorem coefficientEquiv_tensor (e : M ≅ N) (w : D)
    (v : C) (g : J.obj v ⟶ w) (m : M.obj v) :
    coefficientEquiv J e w (tensor J M v g m) = tensor J N v g (e.hom.app v m) :=
  coefficientMap_tensor J e.hom w v g m

end OddMath.QuiverHecke.ELVOld.BalancedInduction
