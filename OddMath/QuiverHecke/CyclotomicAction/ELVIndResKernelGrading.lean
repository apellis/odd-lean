import OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelTensorGrading

/-! # Grading of the induction-restriction coefficient kernel

The concrete ordinary-right grading input for the kernel tensor step in
DeformedMatrixComparison, section 4. The coefficient space is the existing
balanced-induction superspace. Precomposition by a homogeneous source arrow
has that arrow's parity, including the full coefficient parity.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.IndResKernel
universe u
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D] [Supercategory k D]

instance homModule_additive (v : D) : (homModule (k := k) v).Additive where
  map_add {w z} f g := by
    apply LinearMap.ext
    intro b
    exact Preadditive.comp_add v w z b f g

instance homModule_linear (v : D) : (homModule (k := k) v).Linear k where
  map_smul {w z} f r := by
    apply LinearMap.ext
    intro b
    exact Linear.comp_smul v w z b r f

instance homModule_super (v : D) : IsSuperfunctor k (homModule (k := k) v) where
  map_mem := by
    intro w z p f hf
    apply SVec.mem_parityHom_of_apply_mem
    intro q b hb
    change b ∈ (homSVec k D v w).part q at hb
    change b ≫ f ∈ (homSVec k D v z).part (q + p)
    exact (mem_homSVec_part_iff k).2
      (comp_mem ((mem_homSVec_part_iff k).1 hb) hf)

variable (J : C ⥤ D)

theorem precompose_add {v w : D} (a b : v ⟶ w) (t : D) :
    precompose (k := k) J (a + b) t =
      precompose (k := k) J a t + precompose (k := k) J b t := by
  apply BalancedInduction.hom_ext
  intro s g c
  change precompose (k := k) J (a + b) t
      (BalancedInduction.tensor J (J ⋙ homModule (k := k) w) s g c) =
    precompose (k := k) J a t
      (BalancedInduction.tensor J (J ⋙ homModule (k := k) w) s g c) +
    precompose (k := k) J b t
      (BalancedInduction.tensor J (J ⋙ homModule (k := k) w) s g c)
  rw [precompose_tensor, precompose_tensor, precompose_tensor, Preadditive.add_comp,
    BalancedInduction.tensor_add_right]

instance kernel_additive (t : D) : (kernel (k := k) J t).Additive where
  map_add {v w} a b := by
    apply ModuleCat.hom_ext
    change precompose (k := k) J (a.unop + b.unop) t =
      precompose (k := k) J a.unop t + precompose (k := k) J b.unop t
    exact precompose_add J a.unop b.unop t

/-- A balanced tensor with the coefficient bound as a raw category arrow. -/
def componentTensor (v t : D) (s : C) (g : J.obj s ⟶ t)
    (b : v ⟶ J.obj s) : Component (k := k) J v t :=
  BalancedInduction.tensor J (J ⋙ homModule (k := k) v) s g b

@[simp] theorem precompose_componentTensor {v w : D} (a : v ⟶ w) (t : D)
    (s : C) (g : J.obj s ⟶ t) (b : w ⟶ J.obj s) :
    precompose (k := k) J a t (componentTensor (k := k) J w t s g b) =
      componentTensor (k := k) J v t s g (a ≫ b) :=
  precompose_tensor J a t s g b

variable [Preadditive C] [Linear k C] [Supercategory k C]
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]

/-- The existing balanced-induction grading on each coefficient module. -/
def coefficientGrading (t : D) :
    BalancedKernelTensor.CoefficientGrading (kernel (k := k) J t) where
  odd v := (BalancedInduction.superspace J (J ⋙ homModule (k := k) v) t).odd
  odd_comp_odd v :=
    (BalancedInduction.superspace J (J ⋙ homModule (k := k) v) t).odd_comp_odd

theorem coefficientSpace_eq (t v : D) :
    BalancedKernelTensor.coefficientSpace (coefficientGrading (k := k) J t) v =
      BalancedInduction.superspace J (J ⋙ homModule (k := k) v) t := rfl

/-- Sum projection with the coefficient exposed as a raw category arrow. -/
theorem component_proj_tensor (v t : D) (q : ZMod 2) (s : C)
    (g : J.obj s ⟶ t) (b : v ⟶ J.obj s) :
    (BalancedInduction.superspace J (J ⋙ homModule (k := k) v) t).proj q
        (componentTensor (k := k) J v t s g b) =
      componentTensor (k := k) J v t s (proj k q g) (proj k 0 b) +
        componentTensor (k := k) J v t s (proj k (q + 1) g) (proj k 1 b) := by
  have h := BalancedInduction.proj_tensor J (J ⋙ homModule (k := k) v) t q s g b
  change _ = BalancedInduction.tensor J (J ⋙ homModule (k := k) v) s
      (proj k q g) ((homSVec k D v (J.obj s)).proj 0 b) +
    BalancedInduction.tensor J (J ⋙ homModule (k := k) v) s
      (proj k (q + 1) g) ((homSVec k D v (J.obj s)).proj 1 b) at h
  simpa only [homSVec_proj, componentTensor] using h

/-- Ordinary precomposition has the source arrow's full parity. -/
theorem precompose_mem {v w : D} {p : ZMod 2} (a : v ⟶ w)
    (ha : a ∈ parity (R := k) v w p) (t : D) :
    (precompose (k := k) J a t :
      BalancedInduction.superspace J (J ⋙ homModule (k := k) w) t ⟶
        BalancedInduction.superspace J (J ⋙ homModule (k := k) v) t) ∈
      parity (R := k)
        (BalancedInduction.superspace J (J ⋙ homModule (k := k) w) t)
        (BalancedInduction.superspace J (J ⋙ homModule (k := k) v) t) p := by
  change ∀ q, precompose (k := k) J a t ∘ₗ
      (BalancedInduction.superspace J (J ⋙ homModule (k := k) w) t).proj q =
    (BalancedInduction.superspace J (J ⋙ homModule (k := k) v) t).proj (q + p) ∘ₗ
      precompose (k := k) J a t
  intro q
  apply BalancedInduction.hom_ext
  intro s g b
  change w ⟶ J.obj s at b
  have h0 := (proj_comp_of_mem_left (R := k) 0 ha b).symm
  have h1 := (proj_comp_of_mem_left (R := k) 1 ha b).symm
  change precompose (k := k) J a t
      ((BalancedInduction.superspace J (J ⋙ homModule (k := k) w) t).proj q
        (componentTensor (k := k) J w t s g b)) =
    (BalancedInduction.superspace J (J ⋙ homModule (k := k) v) t).proj (q + p)
      (precompose (k := k) J a t (componentTensor (k := k) J w t s g b))
  rw [component_proj_tensor, map_add, precompose_componentTensor,
    precompose_componentTensor, precompose_componentTensor, component_proj_tensor]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp only [zero_add, add_zero] at h0 h1 ⊢
    rw [← h0, ← h1]
  · simp only [add_zero, SVec.zmod2_one_add_one] at h0 h1
    simp only [add_assoc, SVec.zmod2_one_add_one, add_zero]
    rw [← h0, ← h1]
    exact add_comm _ _

/-- The coefficient kernel satisfies the ordinary-right graded balance input. -/
theorem isGradedKernel (t : D) :
    BalancedKernelTensor.IsGradedKernel (kernel (k := k) J t)
      (coefficientGrading (k := k) J t) := by
  intro v w p a ha
  exact precompose_mem J a ha t

end OddMath.QuiverHecke.ELVOld.IndResKernel
