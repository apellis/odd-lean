/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQCounitCancelTransport

/-!
# The counit of `ω_q` is invertible

Even invertible modifications of degree zero from both composites of `chevalleyQGlobalCounit` and `chevalleyQGlobalCounitInv` to identity transformations.

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
local notation "B" => TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "G" => chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "H" => TwoSuperfunctor.comp (G) (F)
local notation "E" => chevalleyQGlobalCounit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "J" => chevalleyQGlobalCounitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)

def chevalleyQGlobalCounitCompIso :
    TwoNatTrans.vcomp (E) (J) ≅ TwoNatTrans.id (H) where
  hom := ⟨fun a => (qCounitCancel (chevQ_negWeight_square a.unop.as).symm).hom,
    fun f => qCounitCancel_naturality _ _ f ((H).map f) (chevalleyQReverseHomCounit f)⟩
  inv := ⟨fun a => (qCounitCancel (chevQ_negWeight_square a.unop.as).symm).inv,
    fun {a b} f => by
      let ea : (E).X a ≫ (J).X a ≅ 𝟙 ((H).obj a) :=
        qCounitCancel (chevQ_negWeight_square a.unop.as).symm
      let eb : (E).X b ≫ (J).X b ≅ 𝟙 ((H).obj b) :=
        qCounitCancel (chevQ_negWeight_square b.unop.as).symm
      let xx : (H).map f ≫ ((E).X b ≫ (J).X b) ⟶
          ((E).X a ≫ (J).X a) ≫ (H).map f := (TwoNatTrans.vcomp (E) (J)).x f
      let yy : (H).map f ≫ 𝟙 ((H).obj b) ⟶ 𝟙 ((H).obj a) ≫ (H).map f :=
        (TwoNatTrans.id (H)).x f
      have h : xx ≫ ea.hom ▷ (H).map f = (H).map f ◁ eb.hom ≫ yy :=
        qCounitCancel_naturality _ _ f ((H).map f) (chevalleyQReverseHomCounit f)
      change yy ≫ ea.inv ▷ (H).map f = (H).map f ◁ eb.inv ≫ xx
      rw [← cancel_epi (whiskerLeftIso (R := k) ((H).map f) eb).hom]
      change (H).map f ◁ eb.hom ≫ yy ≫ ea.inv ▷ (H).map f =
        (H).map f ◁ eb.hom ≫ (H).map f ◁ eb.inv ≫ xx
      rw [← Category.assoc, ← h, Category.assoc, hom_inv_whiskerRight k, Category.comp_id,
        ← Category.assoc, whiskerLeft_hom_inv k, Category.id_comp]⟩
  hom_inv_id := TwoNatTrans.hom_ext fun a =>
    (qCounitCancel (chevQ_negWeight_square a.unop.as).symm).hom_inv_id
  inv_hom_id := TwoNatTrans.hom_ext fun a =>
    (qCounitCancel (chevQ_negWeight_square a.unop.as).symm).inv_hom_id

def chevalleyQGlobalCounitInvCompIso :
    TwoNatTrans.vcomp (J) (E) ≅ TwoNatTrans.id (TwoSuperfunctor.id k B) where
  hom := ⟨fun a => (qCounitInvCancel (chevQ_negWeight_square a.unop.as).symm).hom,
    fun f => qCounitInvCancel_naturality _ _ f ((H).map f) (chevalleyQReverseHomCounit f)⟩
  inv := ⟨fun a => (qCounitInvCancel (chevQ_negWeight_square a.unop.as).symm).inv,
    fun {a b} f => by
      let ea : (J).X a ≫ (E).X a ≅ 𝟙 a :=
        qCounitInvCancel (chevQ_negWeight_square a.unop.as).symm
      let eb : (J).X b ≫ (E).X b ≅ 𝟙 b :=
        qCounitInvCancel (chevQ_negWeight_square b.unop.as).symm
      let xx : f ≫ ((J).X b ≫ (E).X b) ⟶ ((J).X a ≫ (E).X a) ≫ f :=
        (TwoNatTrans.vcomp (J) (E)).x f
      let yy : f ≫ 𝟙 b ⟶ 𝟙 a ≫ f := (TwoNatTrans.id (TwoSuperfunctor.id k B)).x f
      have h : xx ≫ ea.hom ▷ f = f ◁ eb.hom ≫ yy :=
        qCounitInvCancel_naturality _ _ f ((H).map f) (chevalleyQReverseHomCounit f)
      change yy ≫ ea.inv ▷ f = f ◁ eb.inv ≫ xx
      rw [← cancel_epi (whiskerLeftIso (R := k) f eb).hom]
      change f ◁ eb.hom ≫ yy ≫ ea.inv ▷ f = f ◁ eb.hom ≫ f ◁ eb.inv ≫ xx
      rw [← Category.assoc, ← h, Category.assoc, hom_inv_whiskerRight k, Category.comp_id,
        ← Category.assoc, whiskerLeft_hom_inv k, Category.id_comp]⟩
  hom_inv_id := TwoNatTrans.hom_ext fun a =>
    (qCounitInvCancel (chevQ_negWeight_square a.unop.as).symm).hom_inv_id
  inv_hom_id := TwoNatTrans.hom_ext fun a =>
    (qCounitInvCancel (chevQ_negWeight_square a.unop.as).symm).inv_hom_id

theorem chevalleyQGlobalCounitCompIso_homogeneous :
    Supermodification.IsHomogeneous
      (chevalleyQGlobalCounitCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).hom 0 0 :=
  fun a => qCounitCancel_homogeneous (chevQ_negWeight_square a.unop.as).symm

theorem chevalleyQGlobalCounitInvCompIso_homogeneous :
    Supermodification.IsHomogeneous
      (chevalleyQGlobalCounitInvCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).hom
      0 0 :=
  fun a => qCounitInvCancel_homogeneous (chevQ_negWeight_square a.unop.as).symm

theorem chevalleyQGlobalCounitCompIso_inv_homogeneous :
    Supermodification.IsHomogeneous
      (chevalleyQGlobalCounitCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).inv 0 0 :=
  fun a => qCounitCancel_inv_homogeneous (chevQ_negWeight_square a.unop.as).symm

theorem chevalleyQGlobalCounitInvCompIso_inv_homogeneous :
    Supermodification.IsHomogeneous
      (chevalleyQGlobalCounitInvCompIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).inv
      0 0 :=
  fun a => qCounitInvCancel_inv_homogeneous (chevQ_negWeight_square a.unop.as).symm
end OddMath.SKM
