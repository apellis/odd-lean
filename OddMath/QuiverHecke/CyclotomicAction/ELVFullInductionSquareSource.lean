/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquare
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionIsoComponents
import OddMath.QuiverHecke.CyclotomicAction.ELVRestrictionCoendCoordinates

/-! # Input-module isomorphisms after a full induction square

The mixed source chart for Brundan–Ellis (1.12) applies a chosen even
restriction-extension isomorphism after the selected append comparison.
Both its raw component and its tensor formula are evaluated before the
content categories and their quotient coefficients are substituted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem sourceRestriction_total
    {k C E : Type u} [CommRing k] [Category.{u} C] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (U : C ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
    {M : Superfunctor k C (SVec k)} {P R : Superfunctor k E (SVec k)}
    (f : M ⟶ (restriction U).obj P) (g : P ⟶ R) (w : C) (b : M.obj w) :
    (f ≫ (restriction U).map g).total w b = g.total (U.obj w) (f.total w b) := by
  rw [Superfunctor.comp_total]
  rfl

private theorem sourceMap_even_tensor
    {k C E : Type u} [CommRing k] [Category.{u} C] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (A : C ⥤ E) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    {M P : Superfunctor k C (SVec k)} (f : M ⟶ P)
    (hf : f ∈ parity (R := k) _ _ 0) (w : E) (s : C) (g : A.obj s ⟶ w) (b : M.obj s) :
    (moduleMap A f).total w (tensor A M.toFunctor s g b) =
      tensor A P.toFunctor s g (f.total s b) := by
  have h := moduleMap_total_tensor_even A f hf w s g b
  have hz := Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide) s
  simpa only [SuperNatTrans.total, hz, add_zero] using h

private def fullSourceCoefficientIso
    {k B : Type u} [CommRing k] [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    (V : B ⥤ B) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
    (G : Superfunctor k B (SVec k)) :
    ((restriction V).obj G).toFunctor ≅ V ⋙ G.toFunctor := Iso.refl _

private def fullSourceCoordinates
    {k B E : Type u} [CommRing k] [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E]
    (T : B ⥤ E) (V : B ⥤ B) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
    (G : Superfunctor k B (SVec k)) (w : E) :
    Obj T ((restriction V).obj G).toFunctor w ≃ₗ[k] Obj T (V ⋙ G.toFunctor) w :=
  coefficientEquiv T (fullSourceCoefficientIso V G) w

private theorem fullSourceCoordinates_tensor
    {k B E : Type u} [CommRing k] [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E]
    (T : B ⥤ E) (V : B ⥤ B) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
    (G : Superfunctor k B (SVec k)) (s : B) (w : E) (g : T.obj s ⟶ w) (b : G.obj (V.obj s)) :
    (fullSourceCoordinates T V G w).toLinearMap
      (tensor T ((restriction V).obj G).toFunctor s g b) = tensor T (V ⋙ G.toFunctor) s g b :=
  coefficientMap_tensor T (fullSourceCoefficientIso V G).hom w s g b

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (h : J ⋙ U = Q ⋙ T) (M : Superfunctor k C (SVec k)) (P : Superfunctor k B (SVec k))
  (e : induced Q M ≅ P)

/-- Ambient induction acts on its own unit tensor by literal postcomposition. -/
theorem fullSourceInduced_map_unit (s : C) (w : B) (g : Q.obj s ⟶ w) (b : M.obj s) :
    (induced Q M).map g (unit Q M.toFunctor s b) = tensor Q M.toFunctor s g b :=
  postcompose_unit Q M.toFunctor g b

/-- The selected restricted square chart is bijective on its complete raw coend. -/
theorem fullSquareRestrictionLinear_bijective (w : A) :
    Function.Bijective (fullSquareRestrictionLinear J U Q T h M w) :=
  coendIsoLinear_bijective J T U M (induced Q M) (fullSquareRestrictionIso J U Q T h M) w

/-- The selected square chart followed by the chosen input isomorphism under induction. -/
def fullSquareSourceIso : induced J M ≅ (restriction U).obj (induced T P) :=
  fullSquareRestrictionIso J U Q T h M ≪≫ (restriction U).mapIso ((induction T).mapIso e)

/-- The selected source chart with raw coend carriers fixed before specialization. -/
def fullSquareSourceLinear (w : A) : Obj J M.toFunctor w →ₗ[k] Obj T P.toFunctor (U.obj w) :=
  coendIsoLinear J T U M P (fullSquareSourceIso J U Q T h M P e) w

/-- The raw source chart is a component of the specified isomorphism, hence bijective. -/
theorem fullSquareSourceLinear_bijective (w : A) :
    Function.Bijective (fullSquareSourceLinear J U Q T h M P e w) :=
  coendIsoLinear_bijective J T U M P (fullSquareSourceIso J U Q T h M P e) w

/-- The whole selected coefficient and input isomorphism survive on every tensor. -/
theorem fullSquareSourceLinear_tensor (he : e.hom ∈ parity (R := k) _ _ 0)
    (s : C) (w : A) (g : J.obj s ⟶ w) (b : M.obj s) :
    fullSquareSourceLinear J U Q T h M P e w (tensor J M.toFunctor s g b) =
      tensor T P.toFunctor (Q.obj s)
        (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g)
        (e.hom.total (Q.obj s) (unit Q M.toFunctor s b)) := by
  have h0 := sourceRestriction_total U (fullSquareRestrictionIso J U Q T h M).hom
    ((induction T).map e.hom) w (tensor J M.toFunctor s g b)
  have hE := fullSquareRestrictionLinear_tensor J U Q T h M s w g b
  have hMap := congrArg (fun z => ((induction T).map e.hom).total (U.obj w) z) hE
  have hInd := sourceMap_even_tensor T e.hom he (U.obj w) (Q.obj s)
    (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g)
    (unit Q M.toFunctor s b)
  set_option backward.dsimp.instances true in
    dsimp only [induction, fullSquareRestrictionLinear] at hMap hInd
  exact h0.trans (hMap.trans hInd)

/-- A chosen input vector formula transfers before the square is specialized. -/
theorem fullSquareSourceLinear_tensor_of_image (he : e.hom ∈ parity (R := k) _ _ 0)
    (s : C) (w : A) (g : J.obj s ⟶ w) (b : M.obj s) (b' : P.obj (Q.obj s))
    (hb : e.hom.total (Q.obj s) (unit Q M.toFunctor s b) = b') :
    fullSquareSourceLinear J U Q T h M P e w (tensor J M.toFunctor s g b) =
      tensor T P.toFunctor (Q.obj s)
        (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g) b' :=
  (fullSquareSourceLinear_tensor J U Q T h M P e he s w g b).trans
    (congrArg (fun x => tensor T P.toFunctor (Q.obj s)
      (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g) x) hb)

/-- Read the selected source isomorphism in ordinary restriction coefficient coordinates. -/
def fullSquareOrdinarySourceLinear (V : B ⥤ B) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
    (G : Superfunctor k B (SVec k)) (a : induced Q M ≅ (restriction V).obj G) (w : A) :
    Obj J M.toFunctor w →ₗ[k] Obj T (V ⋙ G.toFunctor) (U.obj w) :=
  (fullSourceCoordinates T V G (U.obj w)).toLinearMap ∘ₗ
    fullSquareSourceLinear J U Q T h M ((restriction V).obj G) a w

theorem fullSquareOrdinarySourceLinear_bijective
    (V : B ⥤ B) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
    (G : Superfunctor k B (SVec k)) (a : induced Q M ≅ (restriction V).obj G) (w : A) :
    Function.Bijective (fullSquareOrdinarySourceLinear J U Q T h M V G a w) :=
  (fullSourceCoordinates T V G (U.obj w)).bijective.comp
    (fullSquareSourceLinear_bijective J U Q T h M ((restriction V).obj G) a w)

/-- The prescribed input vector formula is retained in ordinary coefficient coordinates. -/
theorem fullSquareOrdinarySourceLinear_tensor_of_image
    (V : B ⥤ B) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
    (G : Superfunctor k B (SVec k)) (a : induced Q M ≅ (restriction V).obj G)
    (ha : a.hom ∈ parity (R := k) _ _ 0) (s : C) (w : A) (g : J.obj s ⟶ w)
    (b : M.obj s) (b' : G.obj (V.obj (Q.obj s)))
    (hb : a.hom.total (Q.obj s) (unit Q M.toFunctor s b) = b') :
    fullSquareOrdinarySourceLinear J U Q T h M V G a w (tensor J M.toFunctor s g b) =
      tensor T (V ⋙ G.toFunctor) (Q.obj s)
        (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g) b' := by
  have hS := fullSquareSourceLinear_tensor_of_image J U Q T h M ((restriction V).obj G)
    a ha s w g b b' hb
  have hMap := congrArg (fullSourceCoordinates T V G (U.obj w)).toLinearMap hS
  have hC := fullSourceCoordinates_tensor T V G (Q.obj s) (U.obj w)
    (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g) b'
  exact hMap.trans hC

/-- Reindex the selected target chart along a specified equality of its output object. -/
def fullSquareTargetLinear (w : A) (z : E) (hz : U.obj w = z) :
    Obj J M.toFunctor w →ₗ[k] Obj T (induced Q M).toFunctor z :=
  postcompose T (induced Q M).toFunctor (eqToHom hz) ∘ₗ
    fullSquareRestrictionLinear J U Q T h M w

theorem fullSquareTargetLinear_bijective (w : A) (z : E) (hz : U.obj w = z) :
    Function.Bijective (fullSquareTargetLinear J U Q T h M w z hz) := by
  subst z
  rw [fullSquareTargetLinear, eqToHom_refl, postcompose_id, LinearMap.id_comp]
  exact fullSquareRestrictionLinear_bijective J U Q T h M w

/-- The object transport is appended to the entire selected coefficient arrow. -/
theorem fullSquareTargetLinear_tensor (s : C) (w : A) (z : E) (hz : U.obj w = z)
    (g : J.obj s ⟶ w) (b : M.obj s) :
    fullSquareTargetLinear J U Q T h M w z hz (tensor J M.toFunctor s g b) =
      tensor T (induced Q M).toFunctor (Q.obj s)
        ((eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g) ≫ eqToHom hz)
        (unit Q M.toFunctor s b) := by
  have hE := fullSquareRestrictionLinear_tensor J U Q T h M s w g b
  have hMap := congrArg (postcompose T (induced Q M).toFunctor (eqToHom hz)) hE
  exact hMap.trans (postcompose_tensor T (induced Q M).toFunctor (eqToHom hz)
    (Q.obj s) (eqToHom (congrArg (fun F : C ⥤ E => F.obj s) h).symm ≫ U.map g)
    (unit Q M.toFunctor s b))

end OddMath.QuiverHecke.ELVOld.BalancedInduction
