import OddMath.QuiverHecke.CyclotomicAction.ELVFiniteKernelTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelTensorGrading
import OddMath.Algebra.FiniteSuperspace

/-! # Grading finite coefficient-kernel families

Pointwise projectors and parity shifts are attached to the existing ordinary
right kernels without changing their actions. The finite balanced-tensor
product comparison preserves the sum grading, including Option(Fin m).
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]

section Shift
variable {K : Cᵒᵖ ⥤ ModuleCat k} (G : CoefficientGrading K)

/-- Parity shift changes only the coefficient projectors, never the right action. -/
def shiftCoefficientGrading (p : ZMod 2) : CoefficientGrading K where
  odd v := coefficientProj G v (1 + p)
  odd_comp_odd v := by
    apply LinearMap.ext
    intro x
    exact coefficientProj_idem G v (1 + p) x

theorem shiftCoefficientGrading_proj (p q : ZMod 2) (v : C) :
    coefficientProj (shiftCoefficientGrading G p) v q = coefficientProj G v (q + p) := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
      ext x <;> simp [shiftCoefficientGrading, coefficientProj]

variable [Preadditive C] [Linear k C] [Supercategory k C]

theorem shiftCoefficientGrading_isGraded (hK : IsGradedKernel K G) (s : ZMod 2) :
    IsGradedKernel K (shiftCoefficientGrading G s) := by
  intro v w p a ha
  change ∀ q, (K.map a.op).hom ∘ₗ coefficientProj (shiftCoefficientGrading G s) w q =
    coefficientProj (shiftCoefficientGrading G s) v (q + p) ∘ₗ (K.map a.op).hom
  intro q
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, shiftCoefficientGrading_proj,
    shiftCoefficientGrading_proj]
  have h := SVec.apply_proj_of_mem (hK v w p a ha) (q + s) x
  change (K.map a.op) (coefficientProj G w (q + s) x) =
    coefficientProj G v ((q + s) + p) ((K.map a.op) x) at h
  simpa only [add_right_comm q p s] using h

end Shift

section Product
variable {ι : Type} (K : ι → Cᵒᵖ ⥤ ModuleCat k)

instance piKernel_additive [Preadditive C] [∀ a, (K a).Additive] : (piKernel K).Additive where
  map_add {v w} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext a
    change (K a).map (f + g) (x a) = (K a).map f (x a) + (K a).map g (x a)
    rw [(K a).map_add]
    rfl

variable (G : ∀ a, CoefficientGrading (K a))

/-- Coordinatewise coefficient grading on the actual product kernel. -/
def piCoefficientGrading : CoefficientGrading (piKernel K) where
  odd v := LinearMap.pi (fun a => (G a).odd v ∘ₗ LinearMap.proj a)
  odd_comp_odd v := by
    apply LinearMap.ext
    intro x
    funext a
    exact LinearMap.congr_fun ((G a).odd_comp_odd v) (x a)

@[simp] theorem piCoefficientGrading_proj (v : C) (q : ZMod 2)
    (x : (piKernel K).obj (op v)) (a : ι) :
    coefficientProj (piCoefficientGrading K G) v q x a = coefficientProj (G a) v q (x a) := by
  rcases parity_eq_zero_or_one q with rfl | rfl <;> rfl

/-- The coefficient superspace is the established pointwise superspace product. -/
theorem piCoefficientGrading_space (v : C) :
    coefficientSpace (piCoefficientGrading K G) v =
      OddMath.FiniteSuperspace.product (fun a => coefficientSpace (G a) v) := rfl

/-- Each coefficient projection is even for the specified pointwise gradings. -/
theorem piProjection_even (a : ι) (v : C) :
    ((piProjection K a).app (op v)).hom ∈
      parity (R := k) (coefficientSpace (piCoefficientGrading K G) v)
        (coefficientSpace (G a) v) 0 := by
  change ∀ q, ((piProjection K a).app (op v)).hom ∘ₗ
      coefficientProj (piCoefficientGrading K G) v q =
    coefficientProj (G a) v (q + 0) ∘ₗ ((piProjection K a).app (op v)).hom
  intro q
  apply LinearMap.ext
  intro x
  rw [add_zero]
  exact piCoefficientGrading_proj K G v q x a

variable [Preadditive C] [Linear k C] [Supercategory k C]

theorem piKernel_isGraded (hK : ∀ a, IsGradedKernel (K a) (G a)) :
    IsGradedKernel (piKernel K) (piCoefficientGrading K G) := by
  intro v w p a ha
  change ∀ q, ((piKernel K).map a.op).hom ∘ₗ coefficientProj (piCoefficientGrading K G) w q =
    coefficientProj (piCoefficientGrading K G) v (q + p) ∘ₗ ((piKernel K).map a.op).hom
  intro q
  apply LinearMap.ext
  intro x
  funext b
  change (K b).map a.op (coefficientProj (piCoefficientGrading K G) w q x b) =
    coefficientProj (piCoefficientGrading K G) v (q + p) ((piKernel K).map a.op x) b
  rw [piCoefficientGrading_proj, piCoefficientGrading_proj]
  have h := SVec.apply_proj_of_mem (hK b v w p a ha) q (x b)
  change (K b).map a.op (coefficientProj (G b) w q (x b)) =
    coefficientProj (G b) v (q + p) ((K b).map a.op (x b)) at h
  exact h

variable [∀ a, (K a).Additive]

/-- Finite coefficient products commute with balanced tensor as even maps. -/
theorem piEquiv_even [Fintype ι] [DecidableEq ι]
    (hK : ∀ a, IsGradedKernel (K a) (G a)) (M : Superfunctor k C (SVec k)) :
    ((piEquiv K M.toFunctor).toLinearMap :
      superspace (piKernel K) (piCoefficientGrading K G) M.toFunctor (piKernel_isGraded K G hK) ⟶
        OddMath.FiniteSuperspace.product (fun a => superspace (K a) (G a) M.toFunctor (hK a))) ∈
      parity (R := k)
        (superspace (piKernel K) (piCoefficientGrading K G) M.toFunctor (piKernel_isGraded K G hK))
        (OddMath.FiniteSuperspace.product (fun a => superspace (K a) (G a) M.toFunctor (hK a))) 0 := by
  exact OddMath.FiniteSuperspace.assembleRows_even
    (superspace (piKernel K) (piCoefficientGrading K G) M.toFunctor (piKernel_isGraded K G hK))
    (fun a => superspace (K a) (G a) M.toFunctor (hK a))
    (fun a => map M.toFunctor (piProjection K a))
    (fun a => map_even (piKernel K) (piCoefficientGrading K G) M.toFunctor
      (piKernel_isGraded K G hK) (G a) (hK a) (piProjection K a) (piProjection_even K G a))

end Product
end OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
