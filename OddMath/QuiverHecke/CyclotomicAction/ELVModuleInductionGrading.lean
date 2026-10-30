/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTensor

noncomputable section
open CategoryTheory StringDiagrams TensorProduct Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D]
variable (J : C ⥤ D) (M : C ⥤ SVec k)

@[simp] theorem tensor_add_left {w : D} (v : C) (h h' : J.obj v ⟶ w) (m : M.obj v) :
    tensor J M v (h + h') m = tensor J M v h m + tensor J M v h' m := by
  simp [tensor, add_tmul]
@[simp] theorem tensor_add_right {w : D} (v : C) (h : J.obj v ⟶ w) (m m' : M.obj v) :
    tensor J M v h (m + m') = tensor J M v h m + tensor J M v h m' := by
  simp [tensor, tmul_add]
@[simp] theorem tensor_zero_left {w : D} (v : C) (m : M.obj v) :
    tensor J M v (0 : J.obj v ⟶ w) m = 0 := by simp [tensor]
@[simp] theorem tensor_zero_right {w : D} (v : C) (h : J.obj v ⟶ w) :
    tensor J M v h 0 = 0 := by simp [tensor]

variable [Supercategory k D]

def oddSummand (w : D) (v : C) :
    (J.obj v ⟶ w) ⊗[k] M.obj v →ₗ[k] Obj J M w :=
  inclusion J M w v ∘ₗ
    (TensorProduct.map (proj k 1) ((M.obj v).proj 0) +
      TensorProduct.map (proj k 0) ((M.obj v).proj 1))

@[simp] theorem oddSummand_tmul (w : D) (v : C) (h : J.obj v ⟶ w) (m : M.obj v) :
    oddSummand J M w v (h ⊗ₜ[k] m) =
      tensor J M v (proj k 1 h) ((M.obj v).proj 0 m) +
      tensor J M v (proj k 0 h) ((M.obj v).proj 1 m) := by
  simp [oddSummand, tensor]

variable [Preadditive C] [Linear k C] [Supercategory k C]
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [M.Additive] [M.Linear k] [IsSuperfunctor k M]

theorem oddSummand_balance (w : D) (v v' : C) (f : v ⟶ v')
    (h : J.obj v' ⟶ w) (m : M.obj v) :
    oddSummand J M w v ((J.map f ≫ h) ⊗ₜ[k] m) =
      oddSummand J M w v' (h ⊗ₜ[k] M.map f m) := by
  refine Supercategory.induction_on (R := k) f ?_ (fun p f hf => ?_) ?_
  · simp
  ·
    have hj := map_mem J hf
    have hm := map_mem M hf
    have h0 := proj_comp_of_mem_left (R := k) 0 hj h
    have h1 := proj_comp_of_mem_left (R := k) 1 hj h
    have m0 := SVec.apply_proj_of_mem hm 0 m
    have m1 := SVec.apply_proj_of_mem hm 1 m
    rcases parity_eq_zero_or_one p with rfl | rfl
    · simp only [zero_add, add_zero] at h0 h1 m0 m1
      simp only [oddSummand_tmul, h0, h1, ← m0, ← m1, balance]
    · simp only [add_zero, SVec.zmod2_one_add_one, zero_add] at h0 h1 m0 m1
      simp only [oddSummand_tmul, h0, h1, ← m0, ← m1, balance]
      exact add_comm _ _
  · intro f g hf hg
    simpa only [Functor.map_add, Preadditive.add_comp, add_tmul, tmul_add,
      SVec.add_apply, map_add] using congrArg₂ (· + ·) hf hg

def odd (w : D) : Obj J M w →ₗ[k] Obj J M w :=
  lift J M w (oddSummand J M w) (oddSummand_balance J M w)

@[simp] theorem odd_tensor (w : D) (v : C) (h : J.obj v ⟶ w) (m : M.obj v) :
    odd J M w (tensor J M v h m) =
      tensor J M v (proj k 1 h) ((M.obj v).proj 0 m) +
      tensor J M v (proj k 0 h) ((M.obj v).proj 1 m) := by
  simp [odd]

theorem odd_comp_odd (w : D) : odd J M w ∘ₗ odd J M w = odd J M w := by
  apply hom_ext
  intro v h m
  simp [proj_proj, proj_proj_of_ne (R := k) (show (0 : ZMod 2) ≠ 1 by decide),
    proj_proj_of_ne (R := k) (show (1 : ZMod 2) ≠ 0 by decide), SVec.proj_proj_apply]

/-- The sum parity grading on the many-object balanced induction quotient. -/
abbrev superspace (w : D) : SVec k where
  carrier := Obj J M w
  odd := odd J M w
  odd_comp_odd := odd_comp_odd J M w
theorem proj_tensor (w : D) (q : ZMod 2) (v : C)
    (h : J.obj v ⟶ w) (m : M.obj v) :
    (superspace J M w).proj q (tensor J M v h m) =
      tensor J M v (proj k q h) ((M.obj v).proj 0 m) +
      tensor J M v (proj k (q + 1) h) ((M.obj v).proj 1 m) := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · change tensor J M v h m - odd J M w (tensor J M v h m) = _
    rw [odd_tensor]
    have e : tensor J M v h m =
        tensor J M v (proj k 0 h + proj k 1 h)
          ((M.obj v).proj 0 m + (M.obj v).proj 1 m) := by
      rw [Supercategory.proj_add_proj, SVec.proj_apply_add]
    rw [e]
    simp only [tensor_add_left, tensor_add_right, zero_add]
    abel
  · simpa only [SVec.proj_one, SVec.zmod2_one_add_one] using odd_tensor J M w v h m

/-- Postcomposition by a homogeneous arrow has its original parity. -/
theorem postcompose_mem {w z : D} {p : ZMod 2} (a : w ⟶ z)
    (ha : a ∈ parity (R := k) w z p) :
    (postcompose J M a : superspace J M w ⟶ superspace J M z) ∈
      parity (R := k) (superspace J M w) (superspace J M z) p := by
  change ∀ q, postcompose J M a ∘ₗ (superspace J M w).proj q =
    (superspace J M z).proj (q + p) ∘ₗ postcompose J M a
  intro q
  apply hom_ext
  intro v h m
  simp only [LinearMap.comp_apply, proj_tensor J M, map_add, postcompose_tensor]
  rw [proj_comp_of_mem_right (R := k) q h ha]
  rw [show q + p + 1 = (q + 1) + p by abel,
    proj_comp_of_mem_right (R := k) (q + 1) h ha]

/-- Induction as a functor into superspaces, with the quotient grading. -/
def moduleFunctor : D ⥤ SVec k where
  obj := superspace J M
  map := postcompose J M
  map_id := postcompose_id J M
  map_comp := postcompose_comp J M

instance moduleFunctor_additive : (moduleFunctor J M).Additive where
  map_add := by
    intro w z a b
    change postcompose J M (a + b) = postcompose J M a + postcompose J M b
    apply hom_ext
    intro v h m
    simp [Preadditive.comp_add]

instance moduleFunctor_linear : (moduleFunctor J M).Linear k where
  map_smul := by
    intro w z a r
    change postcompose J M (r • a) = r • postcompose J M a
    apply hom_ext
    intro v h m
    rw [LinearMap.smul_apply, postcompose_tensor, Linear.comp_smul]
    change inclusion J M z v ((r • (h ≫ a)) ⊗ₜ[k] m) = _
    rw [← smul_tmul', map_smul, postcompose_tensor]
    rfl

instance moduleFunctor_super : IsSuperfunctor k (moduleFunctor J M) where
  map_mem := postcompose_mem J M _

end OddMath.QuiverHecke.ELVOld.BalancedInduction
