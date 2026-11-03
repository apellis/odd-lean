import OddMath.QuiverHecke.CyclotomicAction.ELVOldInductionBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridDots
import OddMath.QuiverHecke.CyclotomicAction.ELVContentComparisonCoherence

/-! # The chosen old crossing on three successive inductions

Brundan–Ellis Definition 1.5: the canonical induction-composition charts
identify the independently whiskered double-induction crossings with the
direct triple-induction crossings. Their braid is transported through
that same chart, retaining the prescribed negative crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open BalancedInduction
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

private theorem inductionComp_three_hom {k C : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    (J : C ⥤ C) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (M : Superfunctor k C (SVec k)) :
    (induction J).map ((inductionComp J J).hom.app M) ≫
        (inductionComp (J ⋙ J) J).hom.app M =
      (inductionComp J J).hom.app ((induction J).obj M) ≫
        (inductionComp J (J ⋙ J)).hom.app M := by
  simpa only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl,
    Functor.comp_obj, induction] using
    inductionCompOfEq_assoc_hom J J J (J ⋙ J) (J ⋙ J) ((J ⋙ J) ⋙ J)
      rfl rfl rfl rfl M

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (i : I)
local notation "J" => append D Sc cutoff i

/-- The canonical prefix-first flattening of three chosen inductions. -/
def oldTripleFlattening (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (induction J).obj ((induction J).obj ((induction J).obj M)) ≅
      (induction ((J ⋙ J) ⋙ J)).obj M :=
  (induction J).mapIso ((inductionComp J J).app M) ≪≫
    (inductionComp (J ⋙ J) J).app M

theorem oldTripleFlattening_suffix (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (oldTripleFlattening D Sc cutoff i M).hom =
      (inductionComp J J).hom.app ((induction J).obj M) ≫
        (inductionComp J (J ⋙ J)).hom.app M := by
  exact inductionComp_three_hom J M

theorem oldTripleFlattening_prefix_cross
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (induction J).map (equalCrossOnDoubleInduction D Sc cutoff i M) ≫
        (oldTripleFlattening D Sc cutoff i M).hom =
      (oldTripleFlattening D Sc cutoff i M).hom ≫ oldTriplePrefixCross D Sc cutoff i M := by
  exact mapped_conjugated_square (induction J) ((inductionComp J J).app M)
    (transformComponent (equalCross_supernatural D Sc cutoff i) M)
    ((inductionComp (J ⋙ J) J).hom.app M) _
    (inductionComp_inner_dot (J ⋙ J) J (equalCross_supernatural D Sc cutoff i) M)

theorem oldTripleFlattening_suffix_cross
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    equalCrossOnDoubleInduction D Sc cutoff i ((induction J).obj M) ≫
        (oldTripleFlattening D Sc cutoff i M).hom =
      (oldTripleFlattening D Sc cutoff i M).hom ≫ oldTripleSuffixCross D Sc cutoff i M := by
  rw [oldTripleFlattening_suffix]
  exact conjugated_square ((inductionComp J J).app ((induction J).obj M))
    (transformComponent (equalCross_supernatural D Sc cutoff i) ((induction J).obj M))
    ((inductionComp J (J ⋙ J)).hom.app M) _
    (inductionComp_outer_dot J (J ⋙ J) (equalCross_supernatural D Sc cutoff i) M)

/-- Both independent double-induction crossings satisfy the whole braid. -/
theorem oldNestedCross_braid (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (induction J).map (equalCrossOnDoubleInduction D Sc cutoff i M) ≫
        equalCrossOnDoubleInduction D Sc cutoff i ((induction J).obj M) ≫
          (induction J).map (equalCrossOnDoubleInduction D Sc cutoff i M) =
      equalCrossOnDoubleInduction D Sc cutoff i ((induction J).obj M) ≫
        (induction J).map (equalCrossOnDoubleInduction D Sc cutoff i M) ≫
          equalCrossOnDoubleInduction D Sc cutoff i ((induction J).obj M) :=
  braid_of_square (oldTripleFlattening D Sc cutoff i M) _ _ _ _
    (oldTripleFlattening_prefix_cross D Sc cutoff i M)
    (oldTripleFlattening_suffix_cross D Sc cutoff i M)
    (oldTripleCross_braid D Sc cutoff i M)

/-- Evaluation of the chosen signed crossing retains the prescribed minus. -/
theorem signedEqualInductionCross_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (signedEqualInductionCross D Sc cutoff i).total M =
      -equalCrossOnDoubleInduction D Sc cutoff i M := by
  change -((equalCrossOnDoubleInduction_supernatural D Sc cutoff i).toSuperNatTrans.app 0 M) +
      -((equalCrossOnDoubleInduction_supernatural D Sc cutoff i).toSuperNatTrans.app 1 M) = _
  rw [← neg_add]
  exact congrArg Neg.neg (OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (equalCrossOnDoubleInduction_supernatural D Sc cutoff i) M)

/-- The literal negative crossing satisfies the whole nested-induction braid. -/
theorem signedOldNestedCross_braid
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (induction J).map ((signedEqualInductionCross D Sc cutoff i).total M) ≫
        (signedEqualInductionCross D Sc cutoff i).total ((induction J).obj M) ≫
          (induction J).map ((signedEqualInductionCross D Sc cutoff i).total M) =
      (signedEqualInductionCross D Sc cutoff i).total ((induction J).obj M) ≫
        (induction J).map ((signedEqualInductionCross D Sc cutoff i).total M) ≫
          (signedEqualInductionCross D Sc cutoff i).total ((induction J).obj M) := by
  simp only [signedEqualInductionCross_total, Functor.map_neg,
    Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  exact congrArg Neg.neg (oldNestedCross_braid D Sc cutoff i M)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
