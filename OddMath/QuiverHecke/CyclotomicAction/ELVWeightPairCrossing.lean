/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairDots

/-! # Original-weight crossing in the canonical pair coordinates

DeformedActionAssembly §6 needs the independently assembled weight
crossing on the same canonical pair as its two single-letter dots.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem whiskered_comparison_app
    {C A B : Type*} [Category C] [Category A] [Category B]
    (K : C ⥤ A) {F G H L : A ⥤ B} {F' G' : C ⥤ B}
    (e : F' = K ⋙ F) (f : G' = K ⋙ G) (a : F ≅ H) (b : G ≅ L)
    (M : C) (x : H.obj (K.obj M) ⟶ L.obj (K.obj M)) :
    (((eqToIso e ≪≫ Functor.isoWhiskerLeft K a).hom.app M ≫ x) ≫
      (eqToIso f ≪≫ Functor.isoWhiskerLeft K b).inv.app M) =
      eqToHom (Functor.congr_obj e M) ≫
        (a.hom.app (K.obj M) ≫ x ≫ b.inv.app (K.obj M)) ≫
      eqToHom (Functor.congr_obj f M).symm := by
  subst F' G'
  simp only [eqToIso_refl, Iso.refl_trans, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc]

private theorem comparison_component_of_iso_eq
    {C A B : Type*} [Category C] [Category A] [Category B]
    (K : C ⥤ A) {F G H L : A ⥤ B} {F' G' : C ⥤ B}
    (e : F' = K ⋙ F) (f : G' = K ⋙ G) (a : F ≅ H) (b : G ≅ L)
    (c : F' ≅ K ⋙ H) (d : G' ≅ K ⋙ L)
    (hc : c = eqToIso e ≪≫ Functor.isoWhiskerLeft K a)
    (hd : d = eqToIso f ≪≫ Functor.isoWhiskerLeft K b)
    (M : C) (x : H.obj (K.obj M) ⟶ L.obj (K.obj M))
    (q : F'.obj M ⟶ G'.obj M)
    (hq : q = (c.hom.app M ≫ x) ≫ d.inv.app M)
    (r : F.obj (K.obj M) ⟶ G.obj (K.obj M))
    (hr : r = (a.hom.app (K.obj M) ≫ x) ≫ b.inv.app (K.obj M)) :
    q = eqToHom (Functor.congr_obj e M) ≫ r ≫
      eqToHom (Functor.congr_obj f M).symm := by
  subst c d q r
  simpa only [Category.assoc] using whiskered_comparison_app K e f a b M x

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₃)
  (h₃ : x₀ + D.α i = x₂) (h₄ : x₂ + D.α j = x₃)

/-- The chosen weight crossing is the canonical content-pair crossing
under the same two-step object equalities used for the weight dots. -/
def elvWeightCrossVia_contentPair (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :=
  comparison_component_of_iso_eq
    (elvBlockEval D Sc cutoff bound Λ β).toFunctor
    (elvEFunctor_comp₂_contentPair_eq D Sc cutoff bound i j Λ h₁ h₂ β ε hε)
    (elvEFunctor_comp₂_contentPair_eq D Sc cutoff bound j i Λ h₃ h₄ β ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))
    (contentEPairToComparison D Sc cutoff bound β.1 j i ε.1
      (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε))
    (contentEPairToComparison D Sc cutoff bound β.1 i j ε.1
      (elvWeightPair_content_eq D j i Λ h₃ h₄ β ε
        (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε)))
    (elvWeightPairComparison D Sc cutoff bound i j Λ h₁ h₂ β ε hε)
    (elvWeightPairComparison D Sc cutoff bound j i Λ h₃ h₄ β ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))
    (elvWeightPairComparison_eq D Sc cutoff bound i j Λ h₁ h₂ β ε hε)
    (elvWeightPairComparison_eq D Sc cutoff bound j i Λ h₃ h₄ β ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε)) M
    ((contentInductionTransform D Sc cutoff bound
      (elvWeightPair_content_eq D j i Λ h₃ h₄ β ε
        (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))
      (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε)
      (contentCrossAffine_mem D Sc i j)).app (D.parity i * D.parity j) (M β))
    _ (elvWeightCrossVia_component D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄ β ε hε M)
    _ (contentEPairCross_component D Sc cutoff bound β.1 i j ε.1
      (elvWeightPair_content_eq D j i Λ h₃ h₄ β ε
        (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))
      (elvWeightPair_content_eq D i j Λ h₁ h₂ β ε hε) (M β))

end OddMath.QuiverHecke.ELVOld
