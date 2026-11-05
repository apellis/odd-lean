/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCrossingComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightDot
import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairWhiskeredRelations

/-! # Single-letter dots on two original-weight induction steps

Advances `DeformedActionAssembly.md` §6: identify the independently
assembled weight dots at a supported double successor with the actual
single-letter content dots. These comparisons are inputs to the pair
whiskering relations; they do not assume any matrix inverse.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem map_conjugate_eqToHom
    {C B : Type*} [Category C] [Category B] (F : C ⥤ B)
    {a a' : C} {z : B} (h : a = a') (e : z = F.obj a) (e' : z = F.obj a')
    (f : a' ⟶ a') :
    eqToHom e ≫ F.map (eqToHom h ≫ f ≫ eqToHom h.symm) ≫ eqToHom e.symm =
      eqToHom e' ≫ F.map f ≫ eqToHom e'.symm := by
  subst h e
  simp

private theorem family_conjugate_eqToHom
    {C B : Type*} [Category C] [Category B] (F : C ⥤ B)
    (f : ∀ a, F.obj a ⟶ F.obj a) {a a' : C} {z : B}
    (h : a = a') (e : z = F.obj a) (e' : z = F.obj a') :
    eqToHom e ≫ f a ≫ eqToHom e.symm =
      eqToHom e' ≫ f a' ≫ eqToHom e'.symm := by
  subst h e
  simp

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)

/-- The inner weight dot is the induced single-letter content dot, through
the exact supported two-step object equality. -/
theorem elvWeightInnerDot_blockSucc (p : ZMod 2)
    (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvInductionComponent D Sc cutoff bound i Λ h₂
      (blockSucc₂ D i j Λ h₁ h₂ β)).map
        ((elvWeightDot D Sc cutoff bound j Λ h₁).app p M) =
      eqToHom (Functor.congr_obj
        (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) M) ≫
        (elvBlockInd D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₁ β)).map
          ((elvBlockDot D Sc cutoff bound j Λ h₁ β).app p (M β)) ≫
      eqToHom (Functor.congr_obj
        (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) M).symm := by
  rw [elvInductionComponent_map_blockSucc]
  change _ ≫ (elvBlockInd D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₁ β)).map
    (elvWeightDotComponent D Sc cutoff bound j Λ h₁ p M (blockSucc D Λ j h₁ β)) ≫ _ = _
  rw [elvWeightDotComponent_blockSucc]
  exact map_conjugate_eqToHom
    (elvBlockInd D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₁ β)).toFunctor
    (elvInductionComponent_obj_blockSucc D Sc cutoff bound j Λ h₁ β M) _ _ _

/-- The outer weight dot is the dot on the second actual content step,
through the same supported two-step object equality. -/
theorem elvWeightOuterDot_blockSucc (p : ZMod 2)
    (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    elvWeightDotComponent D Sc cutoff bound i Λ h₂ p
      ((elvEFunctor D Sc cutoff bound j Λ h₁).obj M)
      (blockSucc₂ D i j Λ h₁ h₂ β) =
      eqToHom (Functor.congr_obj
        (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) M) ≫
        (elvBlockDot D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₁ β)).app p
          ((elvBlockInd D Sc cutoff bound j Λ h₁ β).obj (M β)) ≫
      eqToHom (Functor.congr_obj
        (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) M).symm := by
  rw [elvWeightDotComponent_blockSucc]
  exact family_conjugate_eqToHom
    (elvBlockInd D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₁ β)).toFunctor
    (fun L => (elvBlockDot D Sc cutoff bound i Λ h₂ (blockSucc D Λ j h₁ β)).app p L)
    (elvInductionComponent_obj_blockSucc D Sc cutoff bound j Λ h₁ β M) _ _

end OddMath.QuiverHecke.ELVOld
