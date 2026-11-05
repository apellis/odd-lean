import OddMath.QuiverHecke.CyclotomicAction.ELVKernelTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionGrading

/-! # Sum parity on coefficient-kernel tensors
The ordinary-right kernel transport in DeformedMatrixComparison §4 retains
the sum grading. Grading data is attached to the kernel's existing modules;
no change of coefficient or quotient module structures is made.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams TensorProduct Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
universe u
variable {k : Type u} [CommRing k] {C : Type u} [Category.{u} C]

/-- Parity projectors on the existing coefficient modules. -/
structure CoefficientGrading (K : Cᵒᵖ ⥤ ModuleCat.{u} k) where
  odd : ∀ v : C, K.obj (op v) →ₗ[k] K.obj (op v)
  odd_comp_odd : ∀ v, odd v ∘ₗ odd v = odd v

def coefficientSpace {K : Cᵒᵖ ⥤ ModuleCat.{u} k} (G : CoefficientGrading K) (v : C) : SVec k where
  carrier := K.obj (op v)
  odd := G.odd v
  odd_comp_odd := G.odd_comp_odd v

def coefficientProj {K : Cᵒᵖ ⥤ ModuleCat.{u} k} (G : CoefficientGrading K)
    (v : C) (q : ZMod 2) : K.obj (op v) →ₗ[k] K.obj (op v) :=
  if q = 0 then LinearMap.id - G.odd v else G.odd v

@[simp] theorem coefficientProj_idem {K : Cᵒᵖ ⥤ ModuleCat.{u} k} (G : CoefficientGrading K)
    (v : C) (q : ZMod 2) (x : K.obj (op v)) :
    coefficientProj G v q (coefficientProj G v q x) = coefficientProj G v q x :=
  SVec.proj_proj_apply (coefficientSpace G v) q x

@[simp] theorem coefficientProj_zero_one {K : Cᵒᵖ ⥤ ModuleCat.{u} k} (G : CoefficientGrading K)
    (v : C) (x : K.obj (op v)) :
    coefficientProj G v 0 (coefficientProj G v 1 x) = 0 :=
  SVec.proj_zero_proj_one (coefficientSpace G v) x

@[simp] theorem coefficientProj_one_zero {K : Cᵒᵖ ⥤ ModuleCat.{u} k} (G : CoefficientGrading K)
    (v : C) (x : K.obj (op v)) :
    coefficientProj G v 1 (coefficientProj G v 0 x) = 0 :=
  SVec.proj_one_proj_zero (coefficientSpace G v) x

theorem coefficientProj_add {K : Cᵒᵖ ⥤ ModuleCat.{u} k} (G : CoefficientGrading K)
    (v : C) (x : K.obj (op v)) :
    coefficientProj G v 0 x + coefficientProj G v 1 x = x :=
  SVec.proj_apply_add (coefficientSpace G v) x

@[simp] theorem tensor_add_left (K : Cᵒᵖ ⥤ ModuleCat.{u} k) (M : C ⥤ SVec k)
    (v : C) (x y : K.obj (op v)) (m : M.obj v) :
    tensor K M v (x + y) m = tensor K M v x m + tensor K M v y m := by
  simp [tensor, add_tmul]

@[simp] theorem tensor_add_right (K : Cᵒᵖ ⥤ ModuleCat.{u} k) (M : C ⥤ SVec k)
    (v : C) (x : K.obj (op v)) (m n : M.obj v) :
    tensor K M v x (m + n) = tensor K M v x m + tensor K M v x n := by
  simp [tensor, tmul_add]

@[simp] theorem tensor_zero_left (K : Cᵒᵖ ⥤ ModuleCat.{u} k) (M : C ⥤ SVec k)
    (v : C) (m : M.obj v) : tensor K M v 0 m = 0 := by simp [tensor]
@[simp] theorem tensor_zero_right (K : Cᵒᵖ ⥤ ModuleCat.{u} k) (M : C ⥤ SVec k)
    (v : C) (x : K.obj (op v)) : tensor K M v x 0 = 0 := by simp [tensor]

variable (K : Cᵒᵖ ⥤ ModuleCat.{u} k) (G : CoefficientGrading K) (M : C ⥤ SVec k)

def oddSummand (v : C) :
    (K.obj (op v)) ⊗[k] M.obj v →ₗ[k] Obj K M :=
  inclusion K M v ∘ₗ
    (TensorProduct.map (coefficientProj G v 1) ((M.obj v).proj 0) +
      TensorProduct.map (coefficientProj G v 0) ((M.obj v).proj 1))

@[simp] theorem oddSummand_tmul (v : C) (x : K.obj (op v)) (m : M.obj v) :
    oddSummand K G M v (x ⊗ₜ[k] m) =
      tensor K M v (coefficientProj G v 1 x) ((M.obj v).proj 0 m) +
      tensor K M v (coefficientProj G v 0 x) ((M.obj v).proj 1 m) := by
  change inclusion K M v
    (TensorProduct.map (coefficientProj G v 1) ((M.obj v).proj 0) (x ⊗ₜ[k] m) +
      TensorProduct.map (coefficientProj G v 0) ((M.obj v).proj 1) (x ⊗ₜ[k] m)) = _
  rw [map_add, TensorProduct.map_tmul, TensorProduct.map_tmul]
  rfl

variable [Preadditive C] [Linear k C] [Supercategory k C]
  [K.Additive] [M.Additive] [M.Linear k] [IsSuperfunctor k M]

/-- Ordinary-right source actions have their specified degree. -/
def IsGradedKernel : Prop :=
  ∀ (v w : C) (p : ZMod 2) (a : v ⟶ w),
    a ∈ parity (R := k) v w p →
      ((K.map a.op).hom : coefficientSpace G w ⟶ coefficientSpace G v) ∈
        parity (R := k) (coefficientSpace G w) (coefficientSpace G v) p

variable (hK : IsGradedKernel K G)
include hK

theorem oddSummand_balance (v w : C) (a : v ⟶ w)
    (x : K.obj (op w)) (m : M.obj v) :
    oddSummand K G M v ((K.map a.op x) ⊗ₜ[k] m) =
      oddSummand K G M w (x ⊗ₜ[k] M.map a m) := by
  refine Supercategory.induction_on (R := k) a ?_ (fun p a ha => ?_) ?_
  · simp
  · have hk := hK v w p a ha
    have hm := map_mem M ha
    have k0 := SVec.apply_proj_of_mem hk 0 x
    have k1 := SVec.apply_proj_of_mem hk 1 x
    change (K.map a.op) (coefficientProj G w 0 x) =
      coefficientProj G v (0 + p) ((K.map a.op) x) at k0
    change (K.map a.op) (coefficientProj G w 1 x) =
      coefficientProj G v (1 + p) ((K.map a.op) x) at k1
    have m0 := SVec.apply_proj_of_mem hm 0 m
    have m1 := SVec.apply_proj_of_mem hm 1 m
    rcases parity_eq_zero_or_one p with rfl | rfl
    · simp only [add_zero] at k0 k1 m0 m1
      simp only [oddSummand_tmul, ← k0, ← k1, ← m0, ← m1, balance]
    · simp only [zero_add, SVec.zmod2_one_add_one] at k0 k1 m0 m1
      simp only [oddSummand_tmul, ← k0, ← k1, ← m0, ← m1, balance]
      exact add_comm _ _
  · intro a b ha hb
    have hkadd : K.map (a + b).op = K.map a.op + K.map b.op := K.map_add
    rw [hkadd, M.map_add]
    change oddSummand K G M v (((K.map a.op) x + (K.map b.op) x) ⊗ₜ[k] m) =
      oddSummand K G M w (x ⊗ₜ[k] ((M.map a) m + (M.map b) m))
    simpa only [add_tmul, tmul_add, map_add] using congrArg₂ (· + ·) ha hb

def odd : Obj K M →ₗ[k] Obj K M :=
  lift K M (oddSummand K G M) (oddSummand_balance K G M hK)

@[simp] theorem odd_tensor (v : C) (x : K.obj (op v)) (m : M.obj v) :
    odd K G M hK (tensor K M v x m) =
      tensor K M v (coefficientProj G v 1 x) ((M.obj v).proj 0 m) +
      tensor K M v (coefficientProj G v 0 x) ((M.obj v).proj 1 m) := by
  rw [odd, lift_tensor, oddSummand_tmul]

theorem odd_comp_odd : odd K G M hK ∘ₗ odd K G M hK = odd K G M hK := by
  apply hom_ext
  intro v x m
  simp [SVec.proj_proj_apply]

/-- Sum parity on the same literal balanced quotient. -/
abbrev superspace : SVec k where
  carrier := Obj K M
  odd := odd K G M hK
  odd_comp_odd := odd_comp_odd K G M hK

theorem proj_tensor (q : ZMod 2) (v : C) (x : K.obj (op v)) (m : M.obj v) :
    (superspace K G M hK).proj q (tensor K M v x m) =
      tensor K M v (coefficientProj G v q x) ((M.obj v).proj 0 m) +
      tensor K M v (coefficientProj G v (q + 1) x) ((M.obj v).proj 1 m) := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · change tensor K M v x m - odd K G M hK (tensor K M v x m) = _
    rw [odd_tensor]
    have e : tensor K M v x m = tensor K M v
        (coefficientProj G v 0 x + coefficientProj G v 1 x)
        ((M.obj v).proj 0 m + (M.obj v).proj 1 m) := by
      rw [coefficientProj_add, SVec.proj_apply_add]
    rw [e]
    simp only [tensor_add_left, tensor_add_right, zero_add]
    abel
  · simpa only [SVec.proj_one, SVec.zmod2_one_add_one] using odd_tensor K G M hK v x m

/-- Even coefficient-kernel maps preserve the quotient sum grading. -/
theorem map_even {L : Cᵒᵖ ⥤ ModuleCat.{u} k} [L.Additive]
    (H : CoefficientGrading L) (hL : IsGradedKernel L H)
    (e : K ⟶ L)
    (he : ∀ v : C, (e.app (op v)).hom ∈
      parity (R := k) (coefficientSpace G v) (coefficientSpace H v) 0) :
    (map M e : superspace K G M hK ⟶ superspace L H M hL) ∈
      parity (R := k) (superspace K G M hK) (superspace L H M hL) 0 := by
  change ∀ q, map M e ∘ₗ (superspace K G M hK).proj q =
    (superspace L H M hL).proj (q + 0) ∘ₗ map M e
  intro q
  rw [add_zero]
  apply hom_ext
  intro v x m
  change map M e ((superspace K G M hK).proj q (tensor K M v x m)) =
    (superspace L H M hL).proj q (map M e (tensor K M v x m))
  rw [proj_tensor, map_add, map_tensor, map_tensor, map_tensor, proj_tensor]
  have h0 := SVec.apply_proj_of_mem (he v) q x
  have h1 := SVec.apply_proj_of_mem (he v) (q + 1) x
  change (e.app (op v)) (coefficientProj G v q x) =
    coefficientProj H v (q + 0) ((e.app (op v)) x) at h0
  change (e.app (op v)) (coefficientProj G v (q + 1) x) =
    coefficientProj H v ((q + 1) + 0) ((e.app (op v)) x) at h1
  simp only [add_zero] at h0 h1
  rw [h0, h1]

end OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
