/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldCyclotomicTarget
import Mathlib.Algebra.DirectSum.Module

/-!
# The signed balanced tensor for the old ELV quotient

The quotient comparison of `DeformedGlobalQP.md` §1, with the full exterior
coefficient algebra. The tensor is the coend of the coefficient-category
Homs with the old cyclotomic quotient. Its balance twists the old action by
total parity. `balancedEquiv` identifies it with `ELVOld.Target`, by pairing
and insertion of the old identity class, without flatness assumptions.
This is the quotient comparison needed for right PBW coordinates; those
coordinates and moving-polynomial cancellation are not asserted here.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The old quotient action, twisted on the acting morphism by total parity. -/
def oldCompose (p : ZMod 2) {v s t : List I} (r : hom D Sc cutoff s t) :
    Old D Sc cutoff v s →ₗ[k] Old D Sc cutoff v t :=
  (ideal D Sc cutoff v s).mapQ (ideal D Sc cutoff v t)
    (Linear.rightComp k _ (twist k p r))
    (fun _ hb => ideal_comp D Sc cutoff hb _)

@[simp] theorem oldCompose_mk (p : ZMod 2) {v s t : List I}
    (r : hom D Sc cutoff s t) (b : hom D Sc cutoff v s) :
    oldCompose D Sc cutoff p r ((ideal D Sc cutoff v s).mkQ b) =
      (ideal D Sc cutoff v t).mkQ (b ≫ twist k p r) := rfl

/-- Ordinary module tensors, indexed by the intermediate old word. -/
abbrev TensorSum (i : I) (v w : List I) :=
  ⨁ t : List I, hom D Sc cutoff (i :: t) w ⊗[k] Old D Sc cutoff v t

/-- A pure tensor in the summand specified by its old intermediate word. -/
def tensorIn (i : I) {v t w : List I} (h : hom D Sc cutoff (i :: t) w)
    (b : Old D Sc cutoff v t) : TensorSum D Sc cutoff i v w :=
  DirectSum.lof k (List I) (fun t => hom D Sc cutoff (i :: t) w ⊗[k]
    Old D Sc cutoff v t) t (h ⊗ₜ[k] b)

/-- Only old-category balance is imposed, with the prescribed total-parity twist. -/
def balanceRelations (p : ZMod 2) (i : I) (v w : List I) :
    Submodule k (TensorSum D Sc cutoff i v w) :=
  Submodule.span k {z | ∃ s t, ∃ h : hom D Sc cutoff (i :: t) w,
    ∃ r : hom D Sc cutoff s t, ∃ b : Old D Sc cutoff v s,
      tensorIn D Sc cutoff i (insert D Sc cutoff i s t r ≫ h) b -
        tensorIn D Sc cutoff i h (oldCompose D Sc cutoff p r b) = z}

/-- The balanced tensor with the full old ELV coefficient module. -/
abbrev BalancedTensor (p : ZMod 2) (i : I) (v w : List I) :=
  TensorSum D Sc cutoff i v w ⧸ balanceRelations D Sc cutoff p i v w

def balancedTmul (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : Old D Sc cutoff v t) :
    BalancedTensor D Sc cutoff p i v w :=
  (balanceRelations D Sc cutoff p i v w).mkQ (tensorIn D Sc cutoff i h b)

theorem balancedTmul_balance (p : ZMod 2) (i : I) {v s t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (r : hom D Sc cutoff s t)
    (b : Old D Sc cutoff v s) :
    balancedTmul D Sc cutoff p i (insert D Sc cutoff i s t r ≫ h) b =
      balancedTmul D Sc cutoff p i h (oldCompose D Sc cutoff p r b) := by
  apply sub_eq_zero.mp
  rw [balancedTmul, balancedTmul, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.subset_span ⟨s, t, h, r, b, rfl⟩)

private def pairBilinear (p : ZMod 2) (i : I) (v t w : List I) :
    hom D Sc cutoff (i :: t) w →ₗ[k]
      Old D Sc cutoff v t →ₗ[k] Target D Sc cutoff i v w where
  toFun := pair D Sc cutoff p i
  map_add' h h' := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
    simp only [LinearMap.add_apply, pair_mk, Preadditive.comp_add, map_add]
  map_smul' c h := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
    simp only [LinearMap.smul_apply, pair_mk, Linear.comp_smul, map_smul,
      RingHom.id_apply]

private def tensorSumPair (p : ZMod 2) (i : I) (v w : List I) :
    TensorSum D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  DirectSum.toModule k (List I) _
    (fun t => TensorProduct.lift (pairBilinear D Sc cutoff p i v t w))

private theorem tensorSumPair_in (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : Old D Sc cutoff v t) :
    tensorSumPair D Sc cutoff p i v w (tensorIn D Sc cutoff i h b) =
      pair D Sc cutoff p i h b := by
  simp [tensorSumPair, tensorIn, pairBilinear]

/-- The pairing descends through the signed old-category balance relations. -/
def balancedForward (p : ZMod 2) (i : I) (v w : List I) :
    BalancedTensor D Sc cutoff p i v w →ₗ[k] Target D Sc cutoff i v w :=
  (balanceRelations D Sc cutoff p i v w).liftQ (tensorSumPair D Sc cutoff p i v w) (by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, t, h, r, b, rfl⟩
    change tensorSumPair D Sc cutoff p i v w _ = 0
    rw [map_sub, tensorSumPair_in, tensorSumPair_in, sub_eq_zero]
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v s).mkQ_surjective b
    exact pair_balance D Sc cutoff p i h r b)

@[simp] theorem balancedForward_tmul (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : Old D Sc cutoff v t) :
    balancedForward D Sc cutoff p i v w (balancedTmul D Sc cutoff p i h b) =
      pair D Sc cutoff p i h b := tensorSumPair_in D Sc cutoff p i h b

private def identityTensor (p : ZMod 2) (i : I) (v w : List I) :
    hom D Sc cutoff (i :: v) w →ₗ[k] BalancedTensor D Sc cutoff p i v w :=
  (balanceRelations D Sc cutoff p i v w).mkQ.comp
    ((DirectSum.lof k (List I) _ v).comp
      ((TensorProduct.mk k _ _).flip ((ideal D Sc cutoff v v).mkQ (𝟙 _))))

private theorem identityTensor_in (p : ZMod 2) (i : I) {v w : List I}
    (h : hom D Sc cutoff (i :: v) w) :
    identityTensor D Sc cutoff p i v w h =
      balancedTmul D Sc cutoff p i h ((ideal D Sc cutoff v v).mkQ (𝟙 _)) := rfl

private theorem identityTensor_kills (p : ZMod 2) (i : I) (v w : List I) :
    relations D Sc cutoff i v w ≤ LinearMap.ker (identityTensor D Sc cutoff p i v w) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, r, hr, h, rfl⟩
  change identityTensor D Sc cutoff p i v w _ = 0
  rw [identityTensor_in, balancedTmul_balance, oldCompose_mk, Category.id_comp]
  have hz : (ideal D Sc cutoff v t).mkQ (twist k p r) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (twist_ideal D Sc cutoff p hr)
  rw [hz]
  simp [balancedTmul, tensorIn]

/-- The inverse inserts the old identity class; only the old ideal is killed. -/
def balancedBackward (p : ZMod 2) (i : I) (v w : List I) :
    Target D Sc cutoff i v w →ₗ[k] BalancedTensor D Sc cutoff p i v w :=
  (relations D Sc cutoff i v w).liftQ (identityTensor D Sc cutoff p i v w)
    (identityTensor_kills D Sc cutoff p i v w)

@[simp] theorem balancedBackward_projection (p : ZMod 2) (i : I) {v w : List I}
    (h : hom D Sc cutoff (i :: v) w) :
    balancedBackward D Sc cutoff p i v w (projection D Sc cutoff i v w h) =
      balancedTmul D Sc cutoff p i h ((ideal D Sc cutoff v v).mkQ (𝟙 _)) := rfl

theorem balancedForward_backward (p : ZMod 2) (i : I) (v w : List I)
    (z : Target D Sc cutoff i v w) :
    balancedForward D Sc cutoff p i v w (balancedBackward D Sc cutoff p i v w z) = z := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  rw [balancedBackward_projection, balancedForward_tmul, pair_id]

private theorem backward_forward_tmul (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : Old D Sc cutoff v t) :
    balancedBackward D Sc cutoff p i v w
      (balancedForward D Sc cutoff p i v w (balancedTmul D Sc cutoff p i h b)) =
        balancedTmul D Sc cutoff p i h b := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  rw [balancedForward_tmul, pair_mk, balancedBackward_projection,
    balancedTmul_balance, oldCompose_mk, Category.id_comp, twist_twist]

theorem balancedBackward_forward (p : ZMod 2) (i : I) (v w : List I)
    (z : BalancedTensor D Sc cutoff p i v w) :
    balancedBackward D Sc cutoff p i v w (balancedForward D Sc cutoff p i v w z) = z := by
  obtain ⟨z, rfl⟩ := (balanceRelations D Sc cutoff p i v w).mkQ_surjective z
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of t z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul h b => exact backward_forward_tmul D Sc cutoff p i h b

/-- The full-coefficient signed balanced tensor is the old-only cyclotomic target.
No independence or tensor comparison is assumed. -/
def balancedEquiv (p : ZMod 2) (i : I) (v w : List I) :
    BalancedTensor D Sc cutoff p i v w ≃ₗ[k] Target D Sc cutoff i v w :=
  LinearEquiv.ofLinearMap (balancedForward D Sc cutoff p i v w)
    (balancedBackward D Sc cutoff p i v w)
    (LinearMap.ext (balancedForward_backward D Sc cutoff p i v w))
    (LinearMap.ext (balancedBackward_forward D Sc cutoff p i v w))

@[simp] theorem balancedEquiv_tmul (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : hom D Sc cutoff v t) :
    balancedEquiv D Sc cutoff p i v w
      (balancedTmul D Sc cutoff p i h ((ideal D Sc cutoff v t).mkQ b)) =
        projection D Sc cutoff i v w (insert D Sc cutoff i v t (twist k p b) ≫ h) :=
  balancedForward_tmul D Sc cutoff p i h _

end OddMath.QuiverHecke.ELVOld
