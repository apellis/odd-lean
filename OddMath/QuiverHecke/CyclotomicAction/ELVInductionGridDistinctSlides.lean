import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionSlides
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridDots
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularMate

/-! # Distinct slides through the two chosen induction charts

Brundan–Ellis (1.8): the rectangular positive crossing retains the signed
dot slides through its two prescribed induction-composition charts.
Four categories and all four append functors remain independent.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem rectangular_slide_of_squares
    {k C : Type*} [CommRing k] [Category C] [Preadditive C] [Linear k C]
    {A A' B B' : C} (e : A ≅ A') (f : B ≅ B')
    (c : A' ⟶ B') (x : End B) (x' : End B') (y : End A) (y' : End A')
    (a : k) (hx : x ≫ f.hom = f.hom ≫ x')
    (hy : y ≫ e.hom = e.hom ≫ y') (hs : c ≫ x' = a • (y' ≫ c)) :
    (e.hom ≫ c ≫ f.inv) ≫ x = a • (y ≫ (e.hom ≫ c ≫ f.inv)) := by
  have hx' : x = f.hom ≫ x' ≫ f.inv := by
    calc
      x = (x ≫ f.hom) ≫ f.inv := by simp
      _ = f.hom ≫ x' ≫ f.inv := by rw [hx, Category.assoc]
  have hy' : y = e.hom ≫ y' ≫ e.inv := by
    calc
      y = (y ≫ e.hom) ≫ e.inv := by simp
      _ = e.hom ≫ y' ≫ e.inv := by rw [hy, Category.assoc]
  rw [hx', hy']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc, Linear.comp_smul, Linear.smul_comp] using
    congrArg (fun z => e.hom ≫ z ≫ f.inv) hs

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  {q : ZMod 2} {γ : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ T).obj s}
  (hγ : IsSupernatural k q γ)

/-- The crossing intertwines the chosen inner target dot and outer source dot. -/
theorem rectangularCrossComponent_slide_inner_outer
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s}
    {β : ∀ s, T.obj s ⟶ T.obj s}
    (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β) (a : k)
    (hs : ∀ s, L.map (α s) ≫ γ s = a • (γ s ≫ β (K.obj s)))
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L T hγ N ≫ (induction L).map (dotEnd J hα N) =
      a • (dotEnd T hβ ((induction K).obj N) ≫ rectangularCrossComponent J K L T hγ N) := by
  let e : induced T (induced K N) ≅ induced (K ⋙ T) N := (inductionComp K T).app N
  let f : induced L (induced J N) ≅ induced (J ⋙ L) N := (inductionComp J L).app N
  have he : rectangularCrossComponent J K L T hγ N =
      e.hom ≫ transformComponent hγ N ≫ f.inv := rfl
  have h := rectangular_slide_of_squares e f
    (transformComponent hγ N)
    ((induction L).map (dotEnd J hα N)) (transformComponent (hα.whiskerRight L) N)
    (dotEnd T hβ ((induction K).obj N)) (transformComponent (hβ.whiskerLeft K) N) a
    (inductionComp_inner_dot J L hα N) (inductionComp_outer_dot K T hβ N)
    (transformComponent_rectangular_slide (hα.whiskerRight L) hγ (hβ.whiskerLeft K) a hs N)
  rw [he]
  convert! h using 1

/-- The crossing also intertwines the chosen outer target dot and inner source dot. -/
theorem rectangularCrossComponent_slide_outer_inner
    {p : ZMod 2} {α : ∀ s, L.obj s ⟶ L.obj s}
    {β : ∀ s, K.obj s ⟶ K.obj s}
    (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β) (a : k)
    (hs : ∀ s, α (J.obj s) ≫ γ s = a • (γ s ≫ T.map (β s)))
    (N : Superfunctor k C (SVec k)) :
    rectangularCrossComponent J K L T hγ N ≫ dotEnd L hα ((induction J).obj N) =
      a • ((induction T).map (dotEnd K hβ N) ≫ rectangularCrossComponent J K L T hγ N) := by
  let e : induced T (induced K N) ≅ induced (K ⋙ T) N := (inductionComp K T).app N
  let f : induced L (induced J N) ≅ induced (J ⋙ L) N := (inductionComp J L).app N
  have he : rectangularCrossComponent J K L T hγ N =
      e.hom ≫ transformComponent hγ N ≫ f.inv := rfl
  have h := rectangular_slide_of_squares e f
    (transformComponent hγ N)
    (dotEnd L hα ((induction J).obj N)) (transformComponent (hα.whiskerLeft J) N)
    ((induction T).map (dotEnd K hβ N)) (transformComponent (hβ.whiskerRight T) N) a
    (inductionComp_outer_dot J L hα N) (inductionComp_inner_dot K T hβ N)
    (transformComponent_rectangular_slide (hα.whiskerLeft J) hγ (hβ.whiskerRight T) a hs N)
  rw [he]
  convert! h using 1

end OddMath.QuiverHecke.ELVOld.BalancedInduction
