/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendSuperfunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleAdjunction

/-! # Right append induction of old quotient representables

The existing balanced induction of the old Hom representable is represented
by the appended word. This is the canonical target comparison needed in
DeformedMatrixComparison (4): the mate target is the actual upper old Hom,
rather than an assumed replacement kernel. All full coefficients are retained.
This does not yet transport to the truncated exact-content categories.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (i : I)

namespace OldInductionRepresentable
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "H" v => oldRepresentableFunctor D Sc cutoff v
variable (v : OldCategory D Sc cutoff)

/-- Composition on an unbalanced tensor summand. -/
def pairing (w : OldCategory D Sc cutoff)
    (z : OldCategory D Sc cutoff) :
    ((J).obj z ⟶ w) ⊗[k] (H v).obj z →ₗ[k] ((J).obj v ⟶ w) :=
  TensorProduct.lift {
    toFun := fun h => {
      toFun := fun g => (J).map g ≫ h
      map_add' := by
        intro g g'
        change v ⟶ z at g g'
        change (J).map (g + g') ≫ h = (J).map g ≫ h + (J).map g' ≫ h
        rw [Functor.map_add, Preadditive.add_comp]
      map_smul' := by
        intro r g
        change v ⟶ z at g
        change (J).map (r • g) ≫ h = r • ((J).map g ≫ h)
        rw [Functor.map_smul, Linear.smul_comp] }
    map_add' := by
      intro h h'
      apply LinearMap.ext
      intro g
      exact Preadditive.comp_add ((J).obj v) ((J).obj z) w ((J).map g) h h'
    map_smul' := by
      intro r h
      apply LinearMap.ext
      intro g
      exact Linear.comp_smul ((J).obj v) ((J).obj z) w ((J).map g) r h }

/-- The forward map on the actual balanced quotient. -/
def forward (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J (H v) w →ₗ[k] ((J).obj v ⟶ w) :=
  BalancedInduction.lift J (H v) w (pairing D Sc cutoff i v w) (by
    intro z z' f h g
    change v ⟶ z at g
    change (J).map g ≫ ((J).map f ≫ h) = (J).map (g ≫ f) ≫ h
    rw [Functor.map_comp, Category.assoc])

@[simp] theorem forward_tensor (w : OldCategory D Sc cutoff)
    (z : OldCategory D Sc cutoff) (h : (J).obj z ⟶ w) (g : v ⟶ z) :
    forward D Sc cutoff i v w (BalancedInduction.tensor J (H v) z h g) =
      (J).map g ≫ h := by
  exact BalancedInduction.lift_tensor J (H v) w
    (pairing D Sc cutoff i v w) _ z h g

/-- The inverse inserts the identity at the representing source object. -/
def backward (w : OldCategory D Sc cutoff) :
    ((J).obj v ⟶ w) →ₗ[k] BalancedInduction.Obj J (H v) w :=
  BalancedInduction.inclusion J (H v) w v ∘ₗ
    (TensorProduct.mk k ((J).obj v ⟶ w) ((H v).obj v)).flip (𝟙 v)

@[simp] theorem backward_apply (w : OldCategory D Sc cutoff)
    (h : (J).obj v ⟶ w) :
    backward D Sc cutoff i v w h = BalancedInduction.tensor J (H v) v h (𝟙 v) := rfl

theorem forward_backward (w : OldCategory D Sc cutoff) :
    forward D Sc cutoff i v w ∘ₗ backward D Sc cutoff i v w = LinearMap.id := by
  ext h
  simp

theorem backward_forward (w : OldCategory D Sc cutoff) :
    backward D Sc cutoff i v w ∘ₗ forward D Sc cutoff i v w = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro z h g
  change v ⟶ z at g
  change backward D Sc cutoff i v w
    (forward D Sc cutoff i v w (BalancedInduction.tensor J (H v) z h g)) = _
  rw [forward_tensor, backward_apply]
  have hb := BalancedInduction.balance J (H v) g h (𝟙 v)
  change BalancedInduction.tensor J (H v) v ((J).map g ≫ h) (𝟙 v) =
    BalancedInduction.tensor J (H v) z h (𝟙 v ≫ g) at hb
  dsimp only [LinearMap.id_apply]
  simpa only [Category.id_comp] using hb

/-- Objectwise comparison, with both quotient roundtrips. -/
def equiv (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J (H v) w ≃ₗ[k] ((J).obj v ⟶ w) :=
  LinearEquiv.ofLinearMap (forward D Sc cutoff i v w)
    (backward D Sc cutoff i v w) (forward_backward D Sc cutoff i v w)
    (backward_forward D Sc cutoff i v w)

theorem forward_naturality {w z : OldCategory D Sc cutoff}
    (a : w ⟶ z) :
    forward D Sc cutoff i v z ∘ₗ BalancedInduction.postcompose J (H v) a =
      (oldRepresentableFunctor D Sc cutoff ((J).obj v)).map a ∘ₗ
        forward D Sc cutoff i v w := by
  apply BalancedInduction.hom_ext
  intro t h g
  change v ⟶ t at g
  change forward D Sc cutoff i v z
    (BalancedInduction.postcompose J (H v) a (BalancedInduction.tensor J (H v) t h g)) =
      forward D Sc cutoff i v w (BalancedInduction.tensor J (H v) t h g) ≫ a
  calc
    _ = forward D Sc cutoff i v z (BalancedInduction.tensor J (H v) t (h ≫ a) g) :=
      congrArg (forward D Sc cutoff i v z)
        (BalancedInduction.postcompose_tensor J (H v) a t h g)
    _ = _ := by rw [forward_tensor, forward_tensor, Category.assoc]

theorem backward_naturality {w z : OldCategory D Sc cutoff}
    (a : w ⟶ z) :
    backward D Sc cutoff i v z ∘ₗ
      (oldRepresentableFunctor D Sc cutoff ((J).obj v)).map a =
      BalancedInduction.postcompose J (H v) a ∘ₗ backward D Sc cutoff i v w := by
  apply LinearMap.ext
  intro h
  exact (BalancedInduction.postcompose_tensor J (H v) a v h (𝟙 v)).symm

/-- Inserting the even identity preserves total parity. -/
theorem backward_mem (w : OldCategory D Sc cutoff) :
    (backward D Sc cutoff i v w :
      Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w ⟶
        BalancedInduction.superspace J (H v) w) ∈ parity (R := k)
      (Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w)
      (BalancedInduction.superspace J (H v) w) 0 := by
  change ∀ q, backward D Sc cutoff i v w ∘ₗ
      (Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w).proj q =
    (BalancedInduction.superspace J (H v) w).proj (q + 0) ∘ₗ
      backward D Sc cutoff i v w
  intro q
  apply LinearMap.ext
  intro h
  change (J).obj v ⟶ w at h
  change BalancedInduction.tensor J (H v) v
      ((Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w).proj q h) (𝟙 v) =
    (BalancedInduction.superspace J (H v) w).proj (q + 0)
      (BalancedInduction.tensor J (H v) v h (𝟙 v))
  rw [add_zero]
  have hp := BalancedInduction.proj_tensor J (H v) w q v h (𝟙 v)
  rw [hp]
  have hid0 : ((H v).obj v).proj 0 (𝟙 v) = 𝟙 v := by
    change 𝟙 v - proj k 1 (𝟙 v) = 𝟙 v
    simp [proj_id]
  have hid1 : ((H v).obj v).proj 1 (𝟙 v) = 0 := by
    change proj k 1 (𝟙 v) = 0
    simp only [proj_id, one_ne_zero, ↓reduceIte]
  rw [hid0, hid1, BalancedInduction.tensor_zero_right, add_zero]
  congr 1
  rcases parity_eq_zero_or_one q with rfl | rfl
  · change h - proj k 1 h = proj k 0 h
    exact eq_sub_iff_add_eq.mpr (proj_add_proj h) |>.symm
  · rfl

/-- The forward quotient map is even, including both odd tensor factors. -/
theorem forward_mem (w : OldCategory D Sc cutoff) :
    (forward D Sc cutoff i v w : BalancedInduction.superspace J (H v) w ⟶
      Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w) ∈
      parity (R := k) (BalancedInduction.superspace J (H v) w)
        (Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w) 0 := by
  have hb := backward_mem D Sc cutoff i v w
  change ∀ q, _ at hb ⊢
  intro q
  apply LinearMap.ext
  intro x
  apply (equiv D Sc cutoff i v w).symm.injective
  have h := congrArg (fun f => f (forward D Sc cutoff i v w x)) (hb q)
  change backward D Sc cutoff i v w
      ((Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w).proj q
        (forward D Sc cutoff i v w x)) =
    (BalancedInduction.superspace J (H v) w).proj (q + 0)
      (backward D Sc cutoff i v w (forward D Sc cutoff i v w x)) at h
  have hr (y) : backward D Sc cutoff i v w (forward D Sc cutoff i v w y) = y :=
    congrArg (fun f => f y) (backward_forward D Sc cutoff i v w)
  change backward D Sc cutoff i v w (forward D Sc cutoff i v w
      ((BalancedInduction.superspace J (H v) w).proj q x)) =
    backward D Sc cutoff i v w
      ((Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w).proj (q + 0)
        (forward D Sc cutoff i v w x))
  simpa only [hr, add_zero] using h.symm

/-- The even forward supernatural transformation. -/
def forwardTransform :
    (BalancedInduction.induction J).obj (oldRepresentable D Sc cutoff v) ⟶
      oldRepresentable D Sc cutoff ((J).obj v) :=
  Superfunctor.homMk (IsSupernatural.toSuperNatTrans (p := 0)
    (x := forward D Sc cutoff i v) {
      mem := forward_mem D Sc cutoff i v
      naturality := by
        intro w z q a ha
        simp only [zero_mul, Supercategory.sign_zero, one_smul]
        exact forward_naturality D Sc cutoff i v a })

/-- The even inverse supernatural transformation. -/
def backwardTransform :
    oldRepresentable D Sc cutoff ((J).obj v) ⟶
      (BalancedInduction.induction J).obj (oldRepresentable D Sc cutoff v) :=
  Superfunctor.homMk (IsSupernatural.toSuperNatTrans (p := 0)
    (x := backward D Sc cutoff i v) {
      mem := backward_mem D Sc cutoff i v
      naturality := by
        intro w z q a ha
        simp only [zero_mul, Supercategory.sign_zero, one_smul]
        exact backward_naturality D Sc cutoff i v a })

@[simp] theorem forwardTransform_app (p : ZMod 2)
    (w : OldCategory D Sc cutoff) :
    (forwardTransform D Sc cutoff i v).app p w =
      if p = 0 then forward D Sc cutoff i v w else 0 := rfl

@[simp] theorem backwardTransform_app (p : ZMod 2)
    (w : OldCategory D Sc cutoff) :
    (backwardTransform D Sc cutoff i v).app p w =
      if p = 0 then backward D Sc cutoff i v w else 0 := rfl

/-- Append induction of the covariant old quotient representable is represented by
its appended word. Both maps are even and natural against every target arrow. -/
def iso :
    (BalancedInduction.induction J).obj (oldRepresentable D Sc cutoff v) ≅
      oldRepresentable D Sc cutoff ((J).obj v) where
  hom := forwardTransform D Sc cutoff i v
  inv := backwardTransform D Sc cutoff i v
  hom_inv_id := by
    apply Superfunctor.hom_ext
    intro p w
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Superfunctor.comp_app, forwardTransform_app, backwardTransform_app,
        Superfunctor.id_app_zero, Superfunctor.id_app_one, ↓reduceIte, zero_add, one_ne_zero,
        SVec.zmod2_one_add_one]
    · change backward D Sc cutoff i v w ∘ₗ forward D Sc cutoff i v w +
        (0 : BalancedInduction.Obj J (H v) w →ₗ[k] BalancedInduction.Obj J (H v) w) = LinearMap.id
      rw [add_zero, backward_forward]
    · apply LinearMap.ext
      intro x
      change 0 + backward D Sc cutoff i v w 0 = 0
      rw [map_zero, add_zero]
  inv_hom_id := by
    apply Superfunctor.hom_ext
    intro p w
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Superfunctor.comp_app, forwardTransform_app, backwardTransform_app,
        Superfunctor.id_app_zero, Superfunctor.id_app_one, ↓reduceIte, zero_add, one_ne_zero,
        SVec.zmod2_one_add_one]
    · change forward D Sc cutoff i v w ∘ₗ backward D Sc cutoff i v w +
        (0 : ((J).obj v ⟶ w) →ₗ[k] ((J).obj v ⟶ w)) = LinearMap.id
      rw [add_zero, forward_backward]
    · change (0 : ((J).obj v ⟶ w) →ₗ[k] ((J).obj v ⟶ w)) = 0
      rfl

/-- The actual restriction-induction target is the upper old Hom, canonically. -/
def upperHomEquiv (t : OldCategory D Sc cutoff) :
    ((BalancedInduction.restriction J).obj
      ((BalancedInduction.induction J).obj (oldRepresentable D Sc cutoff v))).obj t ≃ₗ[k]
      ((J).obj v ⟶ (J).obj t) :=
  equiv D Sc cutoff i v ((J).obj t)

theorem upperHomEquiv_tensor (t z : OldCategory D Sc cutoff)
    (h : (J).obj z ⟶ (J).obj t) (g : v ⟶ z) :
    upperHomEquiv D Sc cutoff i v t
      (BalancedInduction.tensor J (H v) z h g) = (J).map g ≫ h :=
  forward_tensor D Sc cutoff i v ((J).obj t) z h g

end OldInductionRepresentable
end OddMath.QuiverHecke.ELVOld
