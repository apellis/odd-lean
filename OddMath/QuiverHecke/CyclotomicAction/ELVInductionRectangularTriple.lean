/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularMate

/-! # Rectangular triple-induction crossing comparisons

Brundan–Ellis (1.9): the prefix-first chosen triple flattening intertwines
both independent rectangular pair crossings with their literal source
whiskers. The intermediate categories on the two sides may differ.
These are comparison identities, without a braid or comparison premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

private theorem rectangular_conjugation_square {C : Type*} [Category* C]
    {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : C} (e₀ : X₀ ≅ Y₀) (e₁ : X₁ ≅ Y₁)
    (f : Y₀ ⟶ Y₁) (g₀ : Y₀ ⟶ Z₀) (g₁ : Y₁ ⟶ Z₁) (h : Z₀ ⟶ Z₁)
    (hs : f ≫ g₁ = g₀ ≫ h) :
    (e₀.hom ≫ f ≫ e₁.inv) ≫ (e₁.hom ≫ g₁) = (e₀.hom ≫ g₀) ≫ h := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hs]

private theorem rectangular_mapped_conjugation_square
    {C A : Type*} [Category* C] [Category* A] (F : C ⥤ A)
    {X₀ X₁ Y₀ Y₁ : C} {Z₀ Z₁ : A} (e₀ : X₀ ≅ Y₀) (e₁ : X₁ ≅ Y₁)
    (f : Y₀ ⟶ Y₁) (g₀ : F.obj Y₀ ⟶ Z₀) (g₁ : F.obj Y₁ ⟶ Z₁) (h : Z₀ ⟶ Z₁)
    (hs : F.map f ≫ g₁ = g₀ ≫ h) :
    F.map (e₀.hom ≫ f ≫ e₁.inv) ≫ (F.map e₁.hom ≫ g₁) =
      (F.map e₀.hom ≫ g₀) ≫ h := by
  simpa only [Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv] using
    rectangular_conjugation_square (F.mapIso e₀) (F.mapIso e₁) (F.map f) g₀ g₁ h hs

section Prefix
variable {k C A A' B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} A'] [Preadditive A'] [Linear k A'] [Supercategory k A']
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (J' : C ⥤ A') [J'.Additive] [J'.Linear k] [IsSuperfunctor k J']
  (K' : A' ⥤ B) [K'.Additive] [K'.Linear k] [IsSuperfunctor k K']
  (L : B ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]

/-- Prefix flattening compares the actual crossing across two different middle categories. -/
theorem inductionTripleFlattening_prefix_rectangular {p : ZMod 2}
    {γ : ∀ s, (J' ⋙ K').obj s ⟶ (J ⋙ K).obj s} (hγ : IsSupernatural k p γ)
    (M : Superfunctor k C (SVec k)) :
    (induction L).map (rectangularCrossComponent J' J K' K hγ M) ≫
        (inductionTripleFlattening J' K' L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        transformComponent (hγ.whiskerRight L) M := by
  change (induction L).map ((inductionComp J K).hom.app M ≫
      transformComponent hγ M ≫ (inductionComp J' K').inv.app M) ≫
      ((induction L).map ((inductionComp J' K').hom.app M) ≫
        (inductionComp (J' ⋙ K') L).hom.app M) =
    ((induction L).map ((inductionComp J K).hom.app M) ≫
      (inductionComp (J ⋙ K) L).hom.app M) ≫ transformComponent (hγ.whiskerRight L) M
  exact rectangular_mapped_conjugation_square (induction L)
    ((inductionComp J K).app M) ((inductionComp J' K').app M) (transformComponent hγ M)
    ((inductionComp (J ⋙ K) L).hom.app M) ((inductionComp (J' ⋙ K') L).hom.app M)
    (transformComponent (hγ.whiskerRight L) M)
    (inductionComp_inner_transform (J' ⋙ K') (J ⋙ K) L hγ M)
end Prefix

section Suffix
variable {k C A B B' E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} B'] [Preadditive B'] [Linear k B'] [Supercategory k B']
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : B ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (K' : A ⥤ B') [K'.Additive] [K'.Linear k] [IsSuperfunctor k K']
  (L' : B' ⥤ E) [L'.Additive] [L'.Linear k] [IsSuperfunctor k L']

/-- The independent last-pair crossing uses the same chosen triple flattening. -/
theorem inductionTripleFlattening_suffix_rectangular {p : ZMod 2}
    {δ : ∀ s, (K' ⋙ L').obj s ⟶ (K ⋙ L).obj s} (hδ : IsSupernatural k p δ)
    (M : Superfunctor k C (SVec k)) :
    rectangularCrossComponent K' K L' L hδ ((induction J).obj M) ≫
        (inductionTripleFlattening J K' L' M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        transformComponent (hδ.whiskerLeft J) M := by
  rw [inductionTripleFlattening_suffix, inductionTripleFlattening_suffix]
  change ((inductionComp K L).hom.app ((induction J).obj M) ≫
      transformComponent hδ ((induction J).obj M) ≫
        (inductionComp K' L').inv.app ((induction J).obj M)) ≫
      ((inductionComp K' L').hom.app ((induction J).obj M) ≫
        (inductionComp J (K' ⋙ L')).hom.app M) =
    ((inductionComp K L).hom.app ((induction J).obj M) ≫
      (inductionComp J (K ⋙ L)).hom.app M) ≫ transformComponent (hδ.whiskerLeft J) M
  exact rectangular_conjugation_square
    ((inductionComp K L).app ((induction J).obj M))
    ((inductionComp K' L').app ((induction J).obj M)) (transformComponent hδ ((induction J).obj M))
    ((inductionComp J (K ⋙ L)).hom.app M) ((inductionComp J (K' ⋙ L')).hom.app M)
    (transformComponent (hδ.whiskerLeft J) M)
    (inductionComp_outer_transform J (K' ⋙ L') (K ⋙ L) hδ M)
end Suffix
end OddMath.QuiverHecke.ELVOld.BalancedInduction
