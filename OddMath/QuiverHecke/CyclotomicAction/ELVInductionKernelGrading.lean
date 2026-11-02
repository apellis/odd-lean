import OddMath.QuiverHecke.CyclotomicAction.ELVKernelTensorGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionKernel

/-! # Grading of the induction Hom kernel
The Hom-kernel comparison in DeformedMatrixComparison §4 preserves the
actual sum parity on the prescribed balanced induction quotient.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D]
  (J : C ⥤ D)

instance inductionKernel_additive [Preadditive C] [J.Additive] (w : D) :
    (inductionKernel (k := k) J w).Additive where
  map_add {v s} a b := by
    ext g
    change J.map (a.unop + b.unop) ≫ g = J.map a.unop ≫ g + J.map b.unop ≫ g
    rw [J.map_add, Preadditive.add_comp]

variable [Supercategory k D]

def inductionKernelGrading (w : D) :
    CoefficientGrading (inductionKernel (k := k) J w) where
  odd v := (Supercategory.homSVec k D (J.obj v) w).odd
  odd_comp_odd v := (Supercategory.homSVec k D (J.obj v) w).odd_comp_odd

theorem inductionKernel_coefficientSpace (w : D) (v : C) :
    coefficientSpace (inductionKernelGrading J w) v =
      Supercategory.homSVec k D (J.obj v) w := rfl

theorem inductionKernel_coefficientProj (w : D) (v : C) (q : ZMod 2) :
    coefficientProj (inductionKernelGrading J w) v q = (proj k q : (J.obj v ⟶ w) →ₗ[k] _) := by
  change (Supercategory.homSVec k D (J.obj v) w).proj q = _
  exact Supercategory.homSVec_proj k (J.obj v) w q

variable [Preadditive C] [Linear k C] [Supercategory k C]
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]

theorem inductionKernel_isGraded (w : D) :
    IsGradedKernel (inductionKernel (k := k) J w) (inductionKernelGrading J w) := by
  intro v s p a ha
  change (Linear.leftComp k w (J.map a) :
      Supercategory.homSVec k D (J.obj s) w ⟶ Supercategory.homSVec k D (J.obj v) w) ∈
    parity (R := k) (Supercategory.homSVec k D (J.obj s) w)
      (Supercategory.homSVec k D (J.obj v) w) p
  apply SVec.mem_parityHom_of_apply_mem
  intro q g hg
  apply (Supercategory.mem_homSVec_part_iff k).2
  change J.map a ≫ g ∈ parity (R := k) (J.obj v) w (q + p)
  have hg' := (Supercategory.mem_homSVec_part_iff k).1 hg
  simpa only [add_comm p q] using comp_mem (map_mem J ha) hg'

/-- The identity of the literal quotients is even for their actual sum gradings. -/
theorem inductionKernelEquiv_even
    (M : Superfunctor k C (SVec k)) (w : D) :
    ((inductionKernelEquiv J M.toFunctor w).toLinearMap :
      superspace (inductionKernel J w) (inductionKernelGrading J w) M.toFunctor
        (inductionKernel_isGraded J w) ⟶ BalancedInduction.superspace J M.toFunctor w) ∈
      parity (R := k)
        (superspace (inductionKernel J w) (inductionKernelGrading J w) M.toFunctor
          (inductionKernel_isGraded J w))
        (BalancedInduction.superspace J M.toFunctor w) 0 := by
  change ∀ q, (inductionKernelEquiv J M.toFunctor w).toLinearMap ∘ₗ
      (superspace (inductionKernel J w) (inductionKernelGrading J w) M.toFunctor
        (inductionKernel_isGraded J w)).proj q =
    (BalancedInduction.superspace J M.toFunctor w).proj (q + 0) ∘ₗ
      (inductionKernelEquiv J M.toFunctor w).toLinearMap
  intro q
  rw [add_zero]
  apply hom_ext
  intro v g b
  change (superspace (inductionKernel J w) (inductionKernelGrading J w) M.toFunctor
      (inductionKernel_isGraded J w)).proj q
      (tensor (inductionKernel J w) M.toFunctor v g b) =
    (BalancedInduction.superspace J M.toFunctor w).proj q
      (BalancedInduction.tensor J M.toFunctor v g b)
  rw [proj_tensor, BalancedInduction.proj_tensor,
    inductionKernel_coefficientProj, inductionKernel_coefficientProj]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
