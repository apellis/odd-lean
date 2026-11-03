import OddMath.QuiverHecke.CyclotomicAction.ELVWeightBraidSuffixComparison
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
private theorem intertwine_product
    {C : Type*} [Category* C] {X Y : C} (e : X ⟶ Y)
    (l r : End X) (a b : End Y)
    (hl : l ≫ e = e ≫ a) (hr : r ≫ e = e ≫ b) :
    (l ≫ r) ≫ e = e ≫ (a ≫ b) := by
  rw [Category.assoc, hr, ← Category.assoc, hl, Category.assoc]
private theorem braid_of_comparison
    {C : Type*} [Category* C] {X Y : C} (e : X ≅ Y)
    (l r : End X) (a b : End Y)
    (hl : l ≫ e.hom = e.hom ≫ a) (hr : r ≫ e.hom = e.hom ≫ b)
    (hb : b ≫ a ≫ b = a ≫ b ≫ a) :
    r ≫ l ≫ r = l ≫ r ≫ l := by
  have hleft := intertwine_product e.hom r (l ≫ r) b (a ≫ b) hr
    (intertwine_product e.hom l r a b hl hr)
  have hright := intertwine_product e.hom l (r ≫ l) a (b ≫ a) hl
    (intertwine_product e.hom r l b a hr hl)
  exact (cancel_mono e.hom).1
    (hleft.trans ((congrArg (fun z => e.hom ≫ z) hb).trans hright.symm))
private theorem braid_total_three
    {k : Type u} [CommRing k] {A B : PiSCat.{u, u, u + 1} k}
    (F : A ⟶ B) (f g h : End F) (M : A) :
    (f ≫ g ≫ h).total M = f.total M ≫ g.total M ≫ h.total M := by
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
