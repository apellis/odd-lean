import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridDots
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridCrossSquare
import OddMath.QuiverHecke.CyclotomicAction.ELVContentComparisonCoherence

/-! # The braid on a changing-category induction grid

Brundan–Ellis Definition 1.5: the selected negative crossings between
three consecutive induction functors satisfy the braid when the literal
source crossings do. Four different categories and both intermediate
functors are retained, as required by the fixed-content probe action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem conjugated_square {C : Type*} [Category C]
    {A B E : C} (e : A ≅ B) (f : End B) (g : B ⟶ E) (h : End E)
    (hs : f ≫ g = g ≫ h) :
    (e.hom ≫ f ≫ e.inv) ≫ (e.hom ≫ g) = (e.hom ≫ g) ≫ h := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hs]

private theorem mapped_conjugated_square {C A : Type*} [Category C] [Category A]
    (F : C ⥤ A) {X Y : C} {Z : A} (e : X ≅ Y) (f : End Y)
    (g : F.obj Y ⟶ Z) (h : End Z) (hs : F.map f ≫ g = g ≫ h) :
    F.map (e.hom ≫ f ≫ e.inv) ≫ (F.map e.hom ≫ g) =
      (F.map e.hom ≫ g) ≫ h := by
  simpa only [Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv] using
    conjugated_square (F.mapIso e) (F.map f) g h hs

private theorem braid_of_square {C : Type*} [Category C] {A B : C}
    (e : A ≅ B) (a b : End A) (c d : End B)
    (ha : a ≫ e.hom = e.hom ≫ c) (hb : b ≫ e.hom = e.hom ≫ d)
    (h : c ≫ d ≫ c = d ≫ c ≫ d) : a ≫ b ≫ a = b ≫ a ≫ b := by
  have he (f : End A) (g : End B) (hg : f ≫ e.hom = e.hom ≫ g) :
      f = e.hom ≫ g ≫ e.inv := by
    calc
      f = (f ≫ e.hom) ≫ e.inv := by simp
      _ = e.hom ≫ g ≫ e.inv := by rw [hg, Category.assoc]
  rw [he a c ha, he b d hb]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc] using congrArg (fun f => e.hom ≫ f ≫ e.inv) h

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : B ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]

private theorem inductionComp_three_hom (M : Superfunctor k C (SVec k)) :
    (induction L).map ((inductionComp J K).hom.app M) ≫
        (inductionComp (J ⋙ K) L).hom.app M =
      (inductionComp K L).hom.app ((induction J).obj M) ≫
        (inductionComp J (K ⋙ L)).hom.app M := by
  simpa only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl,
    Functor.comp_obj, induction] using
    inductionCompOfEq_assoc_hom J K L (J ⋙ K) (K ⋙ L) ((J ⋙ K) ⋙ L)
      rfl rfl rfl rfl M

/-- The chosen prefix-first three-induction flattening. -/
def inductionTripleFlattening (M : Superfunctor k C (SVec k)) :
    (induction L).obj ((induction K).obj ((induction J).obj M)) ≅
      (induction ((J ⋙ K) ⋙ L)).obj M :=
  (induction L).mapIso ((inductionComp J K).app M) ≪≫
    (inductionComp (J ⋙ K) L).app M

theorem inductionTripleFlattening_suffix (M : Superfunctor k C (SVec k)) :
    (inductionTripleFlattening J K L M).hom =
      (inductionComp K L).hom.app ((induction J).obj M) ≫
        (inductionComp J (K ⋙ L)).hom.app M :=
  inductionComp_three_hom J K L M

variable {p : ZMod 2}
  {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  {δ : ∀ s, (K ⋙ L).obj s ⟶ (K ⋙ L).obj s}
  (hγ : IsSupernatural k p γ) (hδ : IsSupernatural k p δ)

/-- Flattening intertwines the independently chosen prefix crossing. -/
theorem inductionTripleFlattening_prefix_cross (M : Superfunctor k C (SVec k)) :
    (induction L).map (gridDoubleCrossComponent J K hγ M) ≫
        (inductionTripleFlattening J K L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        transformComponent (hγ.whiskerRight L) M :=
  mapped_conjugated_square (induction L) ((inductionComp J K).app M)
    (transformComponent hγ M) ((inductionComp (J ⋙ K) L).hom.app M) _
    (inductionComp_inner_dot (J ⋙ K) L hγ M)

/-- The same flattening intertwines the independently chosen suffix crossing. -/
theorem inductionTripleFlattening_suffix_cross (M : Superfunctor k C (SVec k)) :
    gridDoubleCrossComponent K L hδ ((induction J).obj M) ≫
        (inductionTripleFlattening J K L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        transformComponent (hδ.whiskerLeft J) M := by
  rw [inductionTripleFlattening_suffix]
  exact conjugated_square ((inductionComp K L).app ((induction J).obj M))
    (transformComponent hδ ((induction J).obj M))
    ((inductionComp J (K ⋙ L)).hom.app M) _
    (inductionComp_outer_dot J (K ⋙ L) hδ M)

variable (hb : ∀ s, L.map (γ s) ≫ δ (J.obj s) ≫ L.map (γ s) =
  δ (J.obj s) ≫ L.map (γ s) ≫ δ (J.obj s))

include hb in
/-- The physical chosen grid crossings satisfy the whole module-map braid. -/
theorem gridDoubleCrossComponent_braid (M : Superfunctor k C (SVec k)) :
    (induction L).map (gridDoubleCrossComponent J K hγ M) ≫
        gridDoubleCrossComponent K L hδ ((induction J).obj M) ≫
          (induction L).map (gridDoubleCrossComponent J K hγ M) =
      gridDoubleCrossComponent K L hδ ((induction J).obj M) ≫
        (induction L).map (gridDoubleCrossComponent J K hγ M) ≫
          gridDoubleCrossComponent K L hδ ((induction J).obj M) :=
  braid_of_square (inductionTripleFlattening J K L M) _ _ _ _
    (inductionTripleFlattening_prefix_cross J K L hγ M)
    (inductionTripleFlattening_suffix_cross J K L hδ M)
    (transformComponent_braid ((J ⋙ K) ⋙ L) (hγ.whiskerRight L) (hδ.whiskerLeft J) hb M)

include hb in
/-- The prescribed negative grid crossing retains the braid on every input. -/
theorem inductionModuleCross_braid (M : Superfunctor k C (SVec k)) :
    (induction L).map ((inductionModuleCross J K hγ).total M) ≫
        (inductionModuleCross K L hδ).total ((induction J).obj M) ≫
          (induction L).map ((inductionModuleCross J K hγ).total M) =
      (inductionModuleCross K L hδ).total ((induction J).obj M) ≫
        (induction L).map ((inductionModuleCross J K hγ).total M) ≫
          (inductionModuleCross K L hδ).total ((induction J).obj M) := by
  simp only [inductionModuleCross_total, Functor.map_neg,
    Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  exact congrArg Neg.neg (gridDoubleCrossComponent_braid J K L hγ hδ hb M)

end OddMath.QuiverHecke.ELVOld.BalancedInduction
