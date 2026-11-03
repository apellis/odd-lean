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

private theorem conjugate_eqToHom_trans
    {C : Type*} [Category C] {a b c : C}
    (e : a = b) (h : b = c) (q : a = c) (f : c ⟶ c) :
    eqToHom e ≫ (eqToHom h ≫ f ≫ eqToHom h.symm) ≫ eqToHom e.symm =
      eqToHom q ≫ f ≫ eqToHom q.symm := by
  subst e h
  simp

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)

/-- Recasting the intermediate content identifies the induced inner dot
with the independently defined single-letter dot on the canonical pair. -/
theorem contentPairInnerDotTo_eq (β δ γ : Multiset I)
    (hδ : β + ([i] : Multiset I) = δ)
    (hγ : δ + ([j] : Multiset I) = γ)
    (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β) :
    (contentInductionTo D Sc cutoff bound δ [j] γ hγ).map
      ((elvContentDotTo D Sc cutoff bound i β δ hδ).app (D.parity i) M) =
    eqToHom (Functor.congr_obj
      (contentPairInductionTo_eq D Sc cutoff bound β i j δ γ hδ hγ h) M) ≫
      (contentInductionTo D Sc cutoff bound (β + ([i] : Multiset I)) [j] γ
        ((contentPair_sum β i j).symm.trans h)).map
          ((contentInductionDot D Sc cutoff bound β i).app (D.parity i) M) ≫
    eqToHom (Functor.congr_obj
      (contentPairInductionTo_eq D Sc cutoff bound β i j δ γ hδ hγ h) M).symm := by
  subst δ
  change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  rfl

/-- The same intermediate recast identifies the outer single-letter dot. -/
theorem contentPairOuterDotTo_eq (β δ γ : Multiset I)
    (hδ : β + ([i] : Multiset I) = δ)
    (hγ : δ + ([j] : Multiset I) = γ)
    (h : β + ([i,j] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β) :
    (elvContentDotTo D Sc cutoff bound j δ γ hγ).app (D.parity j)
      ((contentInductionTo D Sc cutoff bound β [i] δ hδ).obj M) =
    eqToHom (Functor.congr_obj
      (contentPairInductionTo_eq D Sc cutoff bound β i j δ γ hδ hγ h) M) ≫
      (elvContentDotTo D Sc cutoff bound j (β + ([i] : Multiset I)) γ
        ((contentPair_sum β i j).symm.trans h)).app (D.parity j)
          ((contentE D Sc cutoff bound β i).obj M) ≫
    eqToHom (Functor.congr_obj
      (contentPairInductionTo_eq D Sc cutoff bound β i j δ γ hδ hγ h) M).symm := by
  subst δ
  change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  rfl

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

/-- The actual inner weight dot becomes the independently whiskered inner
content dot through the chosen canonical pair object equality. -/
theorem elvWeightInnerDot_contentPair
    (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    (elvInductionComponent D Sc cutoff bound i Λ h₂
      (blockSucc₂ D i j Λ h₁ h₂ β)).map
        ((elvWeightDot D Sc cutoff bound j Λ h₁).app (D.parity j) M) =
      eqToHom (Functor.congr_obj
        (elvEFunctor_comp₂_contentPair_eq D Sc cutoff bound i j Λ h₁ h₂ β _ rfl) M) ≫
        (contentInductionTo D Sc cutoff bound (β.1 + ([j] : Multiset I)) [i]
          (blockSucc₂ D i j Λ h₁ h₂ β).1
          ((contentPair_sum β.1 j i).symm.trans
            (elvBlockPair_content_eq D i j Λ h₁ h₂ β))).map
          ((contentInductionDot D Sc cutoff bound β.1 j).app (D.parity j) (M β)) ≫
      eqToHom (Functor.congr_obj
        (elvEFunctor_comp₂_contentPair_eq D Sc cutoff bound i j Λ h₁ h₂ β _ rfl) M).symm := by
  have hw := elvWeightInnerDot_blockSucc D Sc cutoff bound i j Λ h₁ h₂
    (D.parity j) β M
  have hc := contentPairInnerDotTo_eq D Sc cutoff bound j i β.1
    (blockSucc D Λ j h₁ β).1 (blockSucc₂ D i j Λ h₁ h₂ β).1
    (elvBlockSucc_content_eq D j Λ h₁ β)
    (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ j h₁ β))
    (elvBlockPair_content_eq D i j Λ h₁ h₂ β) (M β)
  let e := Functor.congr_obj
    (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) M
  have ht := congrArg (fun f : End ((elvBlockPairInd D Sc cutoff bound i j Λ h₁ h₂ β).obj (M β)) =>
    eqToHom e ≫ f ≫ eqToHom e.symm) hc
  exact hw.trans (ht.trans (conjugate_eqToHom_trans e _ _ _))

/-- The actual outer weight dot becomes the independently defined second
content dot through the same canonical pair equality. -/
theorem elvWeightOuterDot_contentPair
    (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    elvWeightDotComponent D Sc cutoff bound i Λ h₂ (D.parity i)
      ((elvEFunctor D Sc cutoff bound j Λ h₁).obj M)
      (blockSucc₂ D i j Λ h₁ h₂ β) =
      eqToHom (Functor.congr_obj
        (elvEFunctor_comp₂_contentPair_eq D Sc cutoff bound i j Λ h₁ h₂ β _ rfl) M) ≫
        (elvContentDotTo D Sc cutoff bound i (β.1 + ([j] : Multiset I))
          (blockSucc₂ D i j Λ h₁ h₂ β).1
          ((contentPair_sum β.1 j i).symm.trans
            (elvBlockPair_content_eq D i j Λ h₁ h₂ β))).app (D.parity i)
          ((contentE D Sc cutoff bound β.1 j).obj (M β)) ≫
      eqToHom (Functor.congr_obj
        (elvEFunctor_comp₂_contentPair_eq D Sc cutoff bound i j Λ h₁ h₂ β _ rfl) M).symm := by
  have hw := elvWeightOuterDot_blockSucc D Sc cutoff bound i j Λ h₁ h₂
    (D.parity i) β M
  have hc := contentPairOuterDotTo_eq D Sc cutoff bound j i β.1
    (blockSucc D Λ j h₁ β).1 (blockSucc₂ D i j Λ h₁ h₂ β).1
    (elvBlockSucc_content_eq D j Λ h₁ β)
    (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ j h₁ β))
    (elvBlockPair_content_eq D i j Λ h₁ h₂ β) (M β)
  let e := Functor.congr_obj
    (elvEFunctor_comp₂_blockSucc D Sc cutoff bound i j Λ h₁ h₂ β) M
  have ht := congrArg (fun f : End ((elvBlockPairInd D Sc cutoff bound i j Λ h₁ h₂ β).obj (M β)) =>
    eqToHom e ≫ f ≫ eqToHom e.symm) hc
  exact hw.trans (ht.trans (conjugate_eqToHom_trans e _ _ _))

end OddMath.QuiverHecke.ELVOld
