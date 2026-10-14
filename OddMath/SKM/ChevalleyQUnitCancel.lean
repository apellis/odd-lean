/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQUnitCancelTransport

/-!
# The unit of `ω_q` is invertible

Even invertible modifications of degree zero from both composites of `chevalleyQGlobalUnit` and `chevalleyQGlobalUnitInv` to identity transformations.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
  BicategoryStruct TwoSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}
local notation "A" => QTwoEnvelope k (UGr D Sc sy hc)
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "G" => chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "H" => TwoSuperfunctor.comp (F) (G)
local notation "J" => chevalleyQGlobalUnit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "K" => chevalleyQGlobalUnitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)

def chevalleyQGlobalUnitCompIso :
    TwoNatTrans.vcomp (J) (K) ≅ TwoNatTrans.id (TwoSuperfunctor.id k A) where
  hom := ⟨fun a => (qUnitCancel (chevQ_negWeight_square a.as).symm).hom,
    fun f => qUnitCancel_naturality _ _ f ((H).map f) (qUnitHomCounit f)⟩
  inv := ⟨fun a => (qUnitCancel (chevQ_negWeight_square a.as).symm).inv,
    fun {a b} f => by
      let ea : (J).X a ≫ (K).X a ≅ 𝟙 a :=
        qUnitCancel (chevQ_negWeight_square a.as).symm
      let eb : (J).X b ≫ (K).X b ≅ 𝟙 b :=
        qUnitCancel (chevQ_negWeight_square b.as).symm
      let xx : f ≫ ((J).X b ≫ (K).X b) ⟶ ((J).X a ≫ (K).X a) ≫ f :=
        (TwoNatTrans.vcomp (J) (K)).x f
      let yy : f ≫ 𝟙 b ⟶ 𝟙 a ≫ f := (TwoNatTrans.id (TwoSuperfunctor.id k A)).x f
      have h : xx ≫ ea.hom ▷ f = f ◁ eb.hom ≫ yy :=
        qUnitCancel_naturality _ _ f ((H).map f) (qUnitHomCounit f)
      change yy ≫ ea.inv ▷ f = f ◁ eb.inv ≫ xx
      rw [← cancel_epi (whiskerLeftIso (R := k) f eb).hom]
      change f ◁ eb.hom ≫ yy ≫ ea.inv ▷ f = f ◁ eb.hom ≫ f ◁ eb.inv ≫ xx
      rw [← Category.assoc, ← h, Category.assoc, hom_inv_whiskerRight k, Category.comp_id,
        ← Category.assoc, whiskerLeft_hom_inv k, Category.id_comp]⟩
  hom_inv_id := TwoNatTrans.hom_ext fun a =>
    (qUnitCancel (chevQ_negWeight_square a.as).symm).hom_inv_id
  inv_hom_id := TwoNatTrans.hom_ext fun a =>
    (qUnitCancel (chevQ_negWeight_square a.as).symm).inv_hom_id

def chevalleyQGlobalUnitInvCompIso :
    TwoNatTrans.vcomp (K) (J) ≅ TwoNatTrans.id (H) where
  hom := ⟨fun a => (qUnitInvCancel (chevQ_negWeight_square a.as).symm).hom,
    fun f => qUnitInvCancel_naturality _ _ f ((H).map f) (qUnitHomCounit f)⟩
  inv := ⟨fun a => (qUnitInvCancel (chevQ_negWeight_square a.as).symm).inv,
    fun {a b} f => by
      let ea : (K).X a ≫ (J).X a ≅ 𝟙 ((H).obj a) :=
        qUnitInvCancel (chevQ_negWeight_square a.as).symm
      let eb : (K).X b ≫ (J).X b ≅ 𝟙 ((H).obj b) :=
        qUnitInvCancel (chevQ_negWeight_square b.as).symm
      let xx : (H).map f ≫ ((K).X b ≫ (J).X b) ⟶
          ((K).X a ≫ (J).X a) ≫ (H).map f := (TwoNatTrans.vcomp (K) (J)).x f
      let yy : (H).map f ≫ 𝟙 ((H).obj b) ⟶ 𝟙 ((H).obj a) ≫ (H).map f :=
        (TwoNatTrans.id (H)).x f
      have h : xx ≫ ea.hom ▷ (H).map f = (H).map f ◁ eb.hom ≫ yy :=
        qUnitInvCancel_naturality _ _ f ((H).map f) (qUnitHomCounit f)
      change yy ≫ ea.inv ▷ (H).map f = (H).map f ◁ eb.inv ≫ xx
      rw [← cancel_epi (whiskerLeftIso (R := k) ((H).map f) eb).hom]
      change (H).map f ◁ eb.hom ≫ yy ≫ ea.inv ▷ (H).map f =
        (H).map f ◁ eb.hom ≫ (H).map f ◁ eb.inv ≫ xx
      rw [← Category.assoc, ← h, Category.assoc, hom_inv_whiskerRight k, Category.comp_id,
        ← Category.assoc, whiskerLeft_hom_inv k, Category.id_comp]⟩
  hom_inv_id := TwoNatTrans.hom_ext fun a =>
    (qUnitInvCancel (chevQ_negWeight_square a.as).symm).hom_inv_id
  inv_hom_id := TwoNatTrans.hom_ext fun a =>
    (qUnitInvCancel (chevQ_negWeight_square a.as).symm).inv_hom_id

theorem chevalleyQGlobalUnitCompIso_homogeneous :
    Supermodification.IsHomogeneous
      (chevalleyQGlobalUnitCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).hom 0 0 :=
  fun a => qUnitCancel_homogeneous (chevQ_negWeight_square a.as).symm

theorem chevalleyQGlobalUnitInvCompIso_homogeneous :
    Supermodification.IsHomogeneous
      (chevalleyQGlobalUnitInvCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).hom
      0 0 :=
  fun a => qUnitInvCancel_homogeneous (chevQ_negWeight_square a.as).symm

theorem chevalleyQGlobalUnitCompIso_inv_homogeneous :
    Supermodification.IsHomogeneous
      (chevalleyQGlobalUnitCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).inv 0 0 :=
  fun a => qUnitCancel_inv_homogeneous (chevQ_negWeight_square a.as).symm

theorem chevalleyQGlobalUnitInvCompIso_inv_homogeneous :
    Supermodification.IsHomogeneous
      (chevalleyQGlobalUnitInvCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).inv
      0 0 :=
  fun a => qUnitInvCancel_inv_homogeneous (chevQ_negWeight_square a.as).symm
end OddMath.SKM
