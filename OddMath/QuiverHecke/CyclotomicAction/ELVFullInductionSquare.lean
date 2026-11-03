/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVContentRestrictionTensor

/-! # A commuting induction square with full upper inclusion

The canonical content chart in Brundan–Ellis (1.12) is the induction
composition comparison followed by restriction along a full inclusion.
Its selected full-inclusion unit and its generator formula are evaluated
before specializing any coefficient quotient or content category.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem blockFullComparison_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Full] [J.Faithful] [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (M : Superfunctor k C (SVec k)) (P : Superfunctor k A (SVec k))
    (e : induced J M ≅ P) (v : C) (b : M.obj v) :
    ((fullyFaithfulUnitIso J M ≪≫
      (restriction J).mapIso e).hom).total v b =
      e.hom.total (J.obj v) (unit J M.toFunctor v b) := by
  have hu : (fullyFaithfulUnitIso J M).hom.total v b =
      unit J M.toFunctor v b := by
    rw [fullyFaithfulUnitIso_hom]
    exact unit_total_apply J M v b
  rw [Iso.trans_hom, Functor.mapIso_hom, Superfunctor.comp_total]
  change ((restriction J).map e.hom).total v
    ((fullyFaithfulUnitIso J M).hom.total v b) = _
  exact congrArg (fun a => ((restriction J).map e.hom).total v a) hu

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (h : J ⋙ U = Q ⋙ T)

/-- The chosen extension comparison on arbitrary supernatural module maps. -/
def fullSquareExtensionIso : induction (k := k) J ⋙ induction U ≅ induction Q ⋙ induction T :=
  inductionComp J U ≪≫ inductionFunctorIsoOfEq (J ⋙ U) (Q ⋙ T) h ≪≫ (inductionComp Q T).symm

/-- Restrict the chosen extension comparison after its selected full-inclusion unit. -/
def fullSquareRestrictionIso (M : Superfunctor k C (SVec k)) :
    induced J M ≅ (restriction U).obj (induced T (induced Q M)) :=
  fullyFaithfulUnitIso U (induced J M) ≪≫
    (restriction U).mapIso ((fullSquareExtensionIso J U Q T h).app M)

omit [U.Full] [U.Faithful] in
private theorem fullSquareExtension_hom_square (M : Superfunctor k C (SVec k)) :
    (fullSquareExtensionIso J U Q T h).hom.app M =
      squareComparison J U Q T h M (induced Q M) (𝟙 _) := by
  have hi := (induction (k := k) T).map_id ((induction (k := k) Q).obj M)
  unfold fullSquareExtensionIso squareComparison
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]
  rw [hi]
  set_option backward.dsimp.instances true in
    dsimp only [induction, Functor.comp_obj] at *
  rw [Category.comp_id]

private theorem fullSquareRestriction_total (M : Superfunctor k C (SVec k)) (w : A)
    (b : (induced J M).obj w) :
    (fullSquareRestrictionIso J U Q T h M).hom.total w b =
      ((fullSquareExtensionIso J U Q T h).hom.app M).total (U.obj w)
        (unit U (induced J M).toFunctor w b) :=
  blockFullComparison_total U (induced J M) (induced T (induced Q M))
    ((fullSquareExtensionIso J U Q T h).app M) w b

/-- The selected comparison with both literal raw coend endpoints fixed. -/
def fullSquareRestrictionLinear (M : Superfunctor k C (SVec k)) (w : A) :
    Obj J M.toFunctor w →ₗ[k] Obj T (induced Q M).toFunctor (U.obj w) :=
  (fullSquareRestrictionIso J U Q T h M).hom.total w

/-- Whole coefficient arrows retain the canonical input inclusion unit. -/
theorem fullSquareRestrictionLinear_tensor (M : Superfunctor k C (SVec k))
    (s : C) (w : A) (g : J.obj s ⟶ w) (b : M.obj s) :
    fullSquareRestrictionLinear J U Q T h M w (tensor J M.toFunctor s g b) =
      tensor T (induced Q M).toFunctor (Q.obj s)
        (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g)
        (unit Q M.toFunctor s b) := by
  have h0 := fullSquareRestriction_total J U Q T h M w (tensor J M.toFunctor s g b)
  have h1 := congrArg (fun f => f.total (U.obj w)
    (unit U (induced J M).toFunctor w (tensor J M.toFunctor s g b)))
    (fullSquareExtension_hom_square J U Q T h M)
  have h2 := squareLinear_tensor J U Q T h M (induced Q M) (𝟙 _) (id_mem _) s w g b
  set_option backward.dsimp.instances true in
    dsimp only [induction, squareLinear] at h2
  rw [Superfunctor.id_app_zero, SVec.id_apply] at h2
  have h3 := h0.trans h1
  unfold fullSquareRestrictionLinear
  rw [unit_apply] at h3
  exact h3.trans h2

end OddMath.QuiverHecke.ELVOld.BalancedInduction
