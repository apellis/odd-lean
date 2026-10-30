/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleRestriction
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! # Underlying balanced induction tensors

The many-object balanced tensor quotient needed for the induction side of
`DeformedActionAssembly.md` §5. This file constructs underlying ground-ring modules,
not a graded induction superfunctor or an adjunction of supercategories.
-/
noncomputable section
open CategoryTheory StringDiagrams TensorProduct
open scoped DirectSum
attribute [local instance] Classical.propDecidable Classical.decEq
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D]
variable (J : C ⥤ D) (M : C ⥤ SVec k)

/-- The unbalanced direct sum over all source objects. -/
abbrev Raw (w : D) := ⨁ v : C, (J.obj v ⟶ w) ⊗[k] (M.obj v)

/-- A pure tensor in its specified summand. -/
def rawTensor {w : D} (v : C) (h : J.obj v ⟶ w) (m : M.obj v) : Raw J M w :=
  DirectSum.lof k C (fun v => (J.obj v ⟶ w) ⊗[k] (M.obj v)) v (h ⊗ₜ[k] m)

/-- Balancing by every source morphism; no parity restriction is imposed. -/
def relations (w : D) : Submodule k (Raw J M w) :=
  Submodule.span k {x | ∃ (v v' : C) (f : v ⟶ v') (h : J.obj v' ⟶ w)
    (m : M.obj v), x = rawTensor J M v (J.map f ≫ h) m -
      rawTensor J M v' h (M.map f m)}

/-- The concrete many-object balanced tensor quotient. -/
abbrev Obj (w : D) := Raw J M w ⧸ relations J M w

/-- The canonical map from a tensor summand to the quotient. -/
def inclusion (w : D) (v : C) :
    (J.obj v ⟶ w) ⊗[k] (M.obj v) →ₗ[k] Obj J M w :=
  (relations J M w).mkQ ∘ₗ DirectSum.lof k C (fun v => (J.obj v ⟶ w) ⊗[k] (M.obj v)) v

def tensor {w : D} (v : C) (h : J.obj v ⟶ w) (m : M.obj v) : Obj J M w :=
  inclusion J M w v (h ⊗ₜ[k] m)

theorem balance {w : D} {v v' : C} (f : v ⟶ v')
    (h : J.obj v' ⟶ w) (m : M.obj v) :
    tensor J M v (J.map f ≫ h) m = tensor J M v' h (M.map f m) := by
  apply sub_eq_zero.mp
  change (relations J M w).mkQ (rawTensor J M v (J.map f ≫ h) m) -
    (relations J M w).mkQ (rawTensor J M v' h (M.map f m)) = 0
  rw [← map_sub]
  apply (Submodule.Quotient.mk_eq_zero (relations J M w)).mpr
  exact Submodule.subset_span ⟨v, v', f, h, m, rfl⟩

variable {V : Type u} [AddCommGroup V] [Module k V]

/-- Descend a family of linear maps out of the tensor summands. -/
def lift (w : D) (q : ∀ v : C, (J.obj v ⟶ w) ⊗[k] (M.obj v) →ₗ[k] V)
    (hq : ∀ (v v' : C) (f : v ⟶ v') (h : J.obj v' ⟶ w) (m : M.obj v),
      q v ((J.map f ≫ h) ⊗ₜ[k] m) = q v' (h ⊗ₜ[k] M.map f m)) :
    Obj J M w →ₗ[k] V :=
  (relations J M w).liftQ (DirectSum.toModule k C V q) (by
    apply Submodule.span_le.mpr
    rintro x ⟨v, v', f, h, m, rfl⟩
    change (DirectSum.toModule k C V q) _ = 0
    simp only [map_sub, rawTensor, DirectSum.toModule_lof]
    exact sub_eq_zero.mpr (hq v v' f h m))

@[simp] theorem lift_tensor (w : D)
    (q : ∀ v : C, (J.obj v ⟶ w) ⊗[k] (M.obj v) →ₗ[k] V) (hq)
    (v : C) (h : J.obj v ⟶ w) (m : M.obj v) :
    lift J M w q hq (tensor J M v h m) = q v (h ⊗ₜ[k] m) := by
  simp [lift, tensor, inclusion]

/-- Maps out of the quotient are determined by pure tensors. -/
@[ext] theorem hom_ext {w : D} {a b : Obj J M w →ₗ[k] V}
    (h : ∀ v (f : J.obj v ⟶ w) (m : M.obj v),
      a (tensor J M v f m) = b (tensor J M v f m)) : a = b := by
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro v
  apply TensorProduct.ext
  ext f m
  exact h v f m

/-- Uniqueness in the balanced universal property. -/
theorem lift_unique (w : D)
    (q : ∀ v : C, (J.obj v ⟶ w) ⊗[k] (M.obj v) →ₗ[k] V) (hq)
    (a : Obj J M w →ₗ[k] V)
    (ha : ∀ v h m, a (tensor J M v h m) = q v (h ⊗ₜ[k] m)) :
    a = lift J M w q hq := by
  apply hom_ext
  intro v h m
  rw [ha, lift_tensor]

/-- Covariance in the target object, on underlying modules. -/
def postcompose {w z : D} (a : w ⟶ z) : Obj J M w →ₗ[k] Obj J M z :=
  lift J M w (fun v => inclusion J M z v ∘ₗ TensorProduct.map
    ({ toFun := fun h => h ≫ a
       map_add' := fun _ _ => Preadditive.add_comp _ _ _ _ _ _
       map_smul' := fun _ _ => Linear.smul_comp _ _ _ _ _ _ } :
      (J.obj v ⟶ w) →ₗ[k] (J.obj v ⟶ z)) LinearMap.id) (by
    intro v v' f h m
    simpa only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.id_apply, Category.assoc, tensor] using
      balance J M f (h ≫ a) m)

@[simp] theorem postcompose_tensor {w z : D} (a : w ⟶ z)
    (v : C) (h : J.obj v ⟶ w) (m : M.obj v) :
    postcompose J M a (tensor J M v h m) = tensor J M v (h ≫ a) m := by
  rw [postcompose, lift_tensor]
  rfl

@[simp] theorem postcompose_id (w : D) :
    postcompose J M (𝟙 w) = LinearMap.id := by
  apply hom_ext
  intro v h m
  simp

theorem postcompose_comp {w z t : D} (a : w ⟶ z) (b : z ⟶ t) :
    postcompose J M (a ≫ b) = postcompose J M b ∘ₗ postcompose J M a := by
  apply hom_ext
  intro v h m
  simp [Category.assoc]

/-- The unit formula before packaging an induced functor. -/
def unit (v : C) : M.obj v →ₗ[k] Obj J M (J.obj v) :=
  inclusion J M (J.obj v) v ∘ₗ TensorProduct.mk k _ _ (𝟙 (J.obj v))

@[simp] theorem unit_apply (v : C) (m : M.obj v) :
    unit J M v m = tensor J M v (𝟙 _) m := rfl

/-- Reconstruction from the unit by target postcomposition. This is the
pure-tensor formula used in the induction-side triangle. -/
theorem postcompose_unit {v : C} {w : D} (h : J.obj v ⟶ w) (m : M.obj v) :
    postcompose J M h (unit J M v m) = tensor J M v h m := by
  rw [unit_apply, postcompose_tensor, Category.id_comp]

/-- Naturality of the unit for all source morphisms. -/
theorem unit_naturality {v v' : C} (f : v ⟶ v') :
    postcompose J M (J.map f) ∘ₗ unit J M v = unit J M v' ∘ₗ M.map f := by
  ext m
  change postcompose J M (J.map f) (unit J M v m) = unit J M v' (M.map f m)
  rw [postcompose_unit, unit_apply]
  simpa only [Category.comp_id] using balance J M f (𝟙 (J.obj v')) m

variable (N : D ⥤ SVec k) [N.Additive] [N.Linear k]

/-- Evaluation on each tensor summand. -/
def evaluationTensor (w : D) (v : C) :
    (J.obj v ⟶ w) ⊗[k] N.obj (J.obj v) →ₗ[k] N.obj w :=
  TensorProduct.lift (N.mapLinearMap (R := k))

/-- The underlying evaluation counit on the balanced quotient of a restriction. -/
def counit (w : D) : Obj J (J ⋙ N) w →ₗ[k] N.obj w :=
  lift J (J ⋙ N) w (evaluationTensor J N w) (by
    intro v v' f h m
    change N.map (J.map f ≫ h) m = N.map h (N.map (J.map f) m)
    rw [N.map_comp]
    rfl)

@[simp] theorem counit_tensor (w : D) (v : C) (h : J.obj v ⟶ w)
    (m : N.obj (J.obj v)) :
    counit J N w (tensor J (J ⋙ N) v h m) = N.map h m := by
  rw [counit, lift_tensor]
  rfl

/-- Naturality of the evaluation counit for all target morphisms. -/
theorem counit_naturality {w z : D} (a : w ⟶ z) :
    counit J N z ∘ₗ postcompose J (J ⋙ N) a = N.map a ∘ₗ counit J N w := by
  apply hom_ext
  intro v h m
  change counit J N z (postcompose J (J ⋙ N) a (tensor J (J ⋙ N) v h m)) =
    N.map a (counit J N w (tensor J (J ⋙ N) v h m))
  rw [postcompose_tensor, counit_tensor, counit_tensor, N.map_comp]
  rfl

/-- The restriction-side triangle, as an equality of underlying linear maps. -/
theorem counit_unit (v : C) :
    counit J N (J.obj v) ∘ₗ unit J (J ⋙ N) v = LinearMap.id := by
  ext m
  change counit J N (J.obj v) (tensor J (J ⋙ N) v (𝟙 _) m) = m
  rw [counit_tensor, N.map_id]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Underlying balanced induction module for right append on the truncated ELV category. -/
abbrev moduleInductionTensor (σ : List I) (M : TruncatedModules D Sc cutoff N)
    (w : TruncatedCategory D Sc cutoff N) :=
  BalancedInduction.Obj (truncatedAppend D Sc cutoff N σ) M.toFunctor w

end OddMath.QuiverHecke.ELVOld
