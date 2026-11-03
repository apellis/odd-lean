/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridBraid

/-! # The three independent dots under triple-induction flattening

Brundan–Ellis (1.9): the one chosen triple flattening intertwines the
first, middle and last independently whiskered induction dots with their
literal source positional transformations. Changing categories and the
ordinary induction-composition isomorphisms are retained throughout.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

private theorem mapped_dot_square
    {C A : Type*} [Category* C] [Category* A] (F : C ⥤ A)
    {X Y : C} {Z : A} (a : End X) (e : X ⟶ Y) (b : End Y)
    (f : F.obj Y ⟶ Z) (c : End Z)
    (ha : a ≫ e = e ≫ b) (hb : F.map b ≫ f = f ≫ c) :
    F.map a ≫ (F.map e ≫ f) = (F.map e ≫ f) ≫ c := by
  rw [← Category.assoc, ← Functor.map_comp, ha, Functor.map_comp,
    Category.assoc, hb, Category.assoc]

private theorem composite_dot_square {C : Type*} [Category* C]
    {X Y Z : C} (a : End X) (e : X ⟶ Y) (b : End Y) (f : Y ⟶ Z) (c : End Z)
    (ha : a ≫ e = e ≫ b) (hb : b ≫ f = f ≫ c) :
    a ≫ (e ≫ f) = (e ≫ f) ≫ c := by
  rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc]

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : B ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]

/-- The actual first dot, mapped by both later inductions, uses the selected triple flattening. -/
theorem inductionTripleFlattening_first_dot {p : ZMod 2}
    {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) :
    (induction L).map ((induction K).map (dotEnd J hα M)) ≫
        (inductionTripleFlattening J K L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        dotEnd ((J ⋙ K) ⋙ L) ((hα.whiskerRight K).whiskerRight L) M :=
  mapped_dot_square (induction L) ((induction K).map (dotEnd J hα M))
    ((inductionComp J K).hom.app M) (dotEnd (J ⋙ K) (hα.whiskerRight K) M)
    ((inductionComp (J ⋙ K) L).hom.app M)
    (dotEnd ((J ⋙ K) ⋙ L) ((hα.whiskerRight K).whiskerRight L) M)
    (inductionComp_inner_dot J K hα M) (inductionComp_inner_dot (J ⋙ K) L (hα.whiskerRight K) M)

/-- The independently chosen middle dot uses that same triple flattening. -/
theorem inductionTripleFlattening_middle_dot {p : ZMod 2}
    {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
    (M : Superfunctor k C (SVec k)) :
    (induction L).map (dotEnd K hβ ((induction J).obj M)) ≫
        (inductionTripleFlattening J K L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        dotEnd ((J ⋙ K) ⋙ L) ((hβ.whiskerLeft J).whiskerRight L) M :=
  mapped_dot_square (induction L) (dotEnd K hβ ((induction J).obj M))
    ((inductionComp J K).hom.app M) (dotEnd (J ⋙ K) (hβ.whiskerLeft J) M)
    ((inductionComp (J ⋙ K) L).hom.app M)
    (dotEnd ((J ⋙ K) ⋙ L) ((hβ.whiskerLeft J).whiskerRight L) M)
    (inductionComp_outer_dot J K hβ M) (inductionComp_inner_dot (J ⋙ K) L (hβ.whiskerLeft J) M)

/-- The independent last dot uses the prefix-first flattening via its proved suffix equality. -/
theorem inductionTripleFlattening_last_dot {p : ZMod 2}
    {γ : ∀ s, L.obj s ⟶ L.obj s} (hγ : IsSupernatural k p γ)
    (M : Superfunctor k C (SVec k)) :
    dotEnd L hγ ((induction K).obj ((induction J).obj M)) ≫
        (inductionTripleFlattening J K L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        dotEnd ((J ⋙ K) ⋙ L) (hγ.whiskerLeft (J ⋙ K)) M := by
  rw [inductionTripleFlattening_suffix]
  exact composite_dot_square
    (dotEnd L hγ ((induction K).obj ((induction J).obj M)))
    ((inductionComp K L).hom.app ((induction J).obj M))
    (dotEnd (K ⋙ L) (hγ.whiskerLeft K) ((induction J).obj M))
    ((inductionComp J (K ⋙ L)).hom.app M)
    (dotEnd ((J ⋙ K) ⋙ L) (hγ.whiskerLeft (J ⋙ K)) M)
    (inductionComp_outer_dot K L hγ ((induction J).obj M))
    (inductionComp_outer_dot J (K ⋙ L) (hγ.whiskerLeft K) M)

end OddMath.QuiverHecke.ELVOld.BalancedInduction
