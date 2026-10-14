/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseTransportUnits

/-!
# Unit axioms for `G_q`

The left and right unit axioms of `G_q`, reflected through `ω_q`.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct TwoSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "B" => TwoSOp k (QTwoEnvelope k (UGr D Sc sy hc))

/-- Left unitor coherence for the exact reverse comparisons. -/
theorem chevalleyQReverse_leftUnitor {a b : B} (f : a ⟶ b) :
    (chevalleyQReverseMapId a).hom ▷ (chevalleyQReverseHom a b).obj f ≫
      (chevalleyQReverseMapComp (𝟙 a) f).hom ≫
      (chevalleyQReverseHom a b).map (leftUnitor f).hom =
    (leftUnitor ((chevalleyQReverseHom a b).obj f)).hom := by
  let P := chevalleyQReverseObj a
  let Q := chevalleyQReverseObj b
  let x : P ⟶ Q := (chevalleyQReverseHom a b).obj f
  let i : P ⟶ P := (chevalleyQReverseHom a a).obj (𝟙 a)
  let z : P ⟶ Q := (chevalleyQReverseHom a b).obj (𝟙 a ≫ f)
  let ci : 𝟙 P ≅ i := chevalleyQReverseMapId a
  let cc : i ≫ x ≅ z := chevalleyQReverseMapComp (𝟙 a) f
  let u : z ⟶ x := (chevalleyQReverseHom a b).map (leftUnitor f).hom
  let tx : (F).obj P ⟶ (F).obj Q := (chevalleyQReverseTransport a b).obj f
  let ti : (F).obj P ⟶ (F).obj P := (chevalleyQReverseTransport a a).obj (𝟙 a)
  let tz : (F).obj P ⟶ (F).obj Q := (chevalleyQReverseTransport a b).obj (𝟙 a ≫ f)
  let ex : (F).map x ≅ tx := chevalleyQReverseHomCounit f
  let ei : (F).map i ≅ ti := chevalleyQReverseHomCounit (𝟙 a)
  let ez : (F).map z ≅ tz := chevalleyQReverseHomCounit (𝟙 a ≫ f)
  let si : 𝟙 ((F).obj P) ≅ ti := (eqToIso (chevalleyQReverseTransport_id a)).symm
  let sc : ti ≫ tx ≅ tz := (eqToIso (chevalleyQReverseTransport_comp (𝟙 a) f)).symm
  let tu : tz ⟶ tx := (chevalleyQReverseTransport a b).map (leftUnitor f).hom
  have hu : (F).map₂ u = ez.hom ≫ tu ≫ ex.inv :=
    chevalleyQReverseHom_map_image (leftUnitor f).hom
  have hi : (F).map₂ ci.hom = ((F).mapId P).inv ≫ si.hom ≫ ei.inv :=
    chevalleyQReverseMapId_image a
  have hc' : (F).map₂ cc.hom = ((F).mapComp i x).inv ≫
      ei.hom ▷ (F).map x ≫ ti ◁ ex.hom ≫ sc.hom ≫ ez.inv :=
    chevalleyQReverseMapComp_image (𝟙 a) f
  have ht : si.hom ▷ tx ≫ sc.hom ≫ tu = (leftUnitor tx).hom :=
    chevQEndpointTransport_leftUnitor (chevQ_negWeight_square a.unop.as).symm
      (chevQ_negWeight_square b.unop.as).symm f
  have he : si.hom ∈ parity (R := k) _ _ 0 :=
    eqToHom_mem (R := k) (C := (F).obj P ⟶ (F).obj P)
      (chevalleyQReverseTransport_id a).symm
  have hw : (F).map₂ (ci.hom ▷ x) = ((F).mapComp (𝟙 P) x).inv ≫
      (F).map₂ ci.hom ▷ (F).map x ≫ ((F).mapComp i x).hom := by
    rw [(F).mapComp_naturality_left, Iso.inv_hom_id_assoc]
  apply (chevQHom (negWeight a.unop.as) (negWeight b.unop.as)).map_injective
  change (F).map₂ (ci.hom ▷ x ≫ cc.hom ≫ u) = (F).map₂ (leftUnitor x).hom
  rw [(F).map₂_comp, (F).map₂_comp, hw, hi, hc', hu]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    comp_whiskerRight' k, inv_hom_whiskerRight_assoc k]
  rw [whisker_exchange_of_even_left_assoc he ex.hom]
  have ht' := congrArg (· ≫ ex.inv) ht
  simp only [Category.assoc] at ht'
  rw [ht', leftUnitor_naturality_assoc k]
  simp only [Iso.hom_inv_id, Category.comp_id]
  rw [← (F).map₂_leftUnitor x]
  simp only [inv_hom_whiskerRight_assoc k, Iso.inv_hom_id_assoc]

/-- Right unitor coherence for the exact reverse comparisons. -/
theorem chevalleyQReverse_rightUnitor {a b : B} (f : a ⟶ b) :
    (chevalleyQReverseHom a b).obj f ◁ (chevalleyQReverseMapId b).hom ≫
      (chevalleyQReverseMapComp f (𝟙 b)).hom ≫
      (chevalleyQReverseHom a b).map (rightUnitor f).hom =
    (rightUnitor ((chevalleyQReverseHom a b).obj f)).hom := by
  let P := chevalleyQReverseObj a
  let Q := chevalleyQReverseObj b
  let x : P ⟶ Q := (chevalleyQReverseHom a b).obj f
  let i : Q ⟶ Q := (chevalleyQReverseHom b b).obj (𝟙 b)
  let z : P ⟶ Q := (chevalleyQReverseHom a b).obj (f ≫ 𝟙 b)
  let ci : 𝟙 Q ≅ i := chevalleyQReverseMapId b
  let cc : x ≫ i ≅ z := chevalleyQReverseMapComp f (𝟙 b)
  let u : z ⟶ x := (chevalleyQReverseHom a b).map (rightUnitor f).hom
  let tx : (F).obj P ⟶ (F).obj Q := (chevalleyQReverseTransport a b).obj f
  let ti : (F).obj Q ⟶ (F).obj Q := (chevalleyQReverseTransport b b).obj (𝟙 b)
  let tz : (F).obj P ⟶ (F).obj Q := (chevalleyQReverseTransport a b).obj (f ≫ 𝟙 b)
  let ex : (F).map x ≅ tx := chevalleyQReverseHomCounit f
  let ei : (F).map i ≅ ti := chevalleyQReverseHomCounit (𝟙 b)
  let ez : (F).map z ≅ tz := chevalleyQReverseHomCounit (f ≫ 𝟙 b)
  let si : 𝟙 ((F).obj Q) ≅ ti := (eqToIso (chevalleyQReverseTransport_id b)).symm
  let sc : tx ≫ ti ≅ tz := (eqToIso (chevalleyQReverseTransport_comp f (𝟙 b))).symm
  let tu : tz ⟶ tx := (chevalleyQReverseTransport a b).map (rightUnitor f).hom
  have hu : (F).map₂ u = ez.hom ≫ tu ≫ ex.inv :=
    chevalleyQReverseHom_map_image (rightUnitor f).hom
  have hi : (F).map₂ ci.hom = ((F).mapId Q).inv ≫ si.hom ≫ ei.inv :=
    chevalleyQReverseMapId_image b
  have hc' : (F).map₂ cc.hom = ((F).mapComp x i).inv ≫
      ex.hom ▷ (F).map i ≫ tx ◁ ei.hom ≫ sc.hom ≫ ez.inv :=
    chevalleyQReverseMapComp_image f (𝟙 b)
  have ht : tx ◁ si.hom ≫ sc.hom ≫ tu = (rightUnitor tx).hom :=
    chevQEndpointTransport_rightUnitor (chevQ_negWeight_square a.unop.as).symm
      (chevQ_negWeight_square b.unop.as).symm f
  have he : ex.hom ∈ parity (R := k) _ _ 0 := chevalleyQReverseHomCounit_even f
  have hw : (F).map₂ (x ◁ ci.hom) = ((F).mapComp x (𝟙 Q)).inv ≫
      (F).map x ◁ (F).map₂ ci.hom ≫ ((F).mapComp x i).hom := by
    rw [(F).mapComp_naturality_right, Iso.inv_hom_id_assoc]
  apply (chevQHom (negWeight a.unop.as) (negWeight b.unop.as)).map_injective
  change (F).map₂ (x ◁ ci.hom ≫ cc.hom ≫ u) = (F).map₂ (rightUnitor x).hom
  rw [(F).map₂_comp, (F).map₂_comp, hw, hc', hu]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [← whisker_exchange_of_even_left_assoc he]
  rw [hi]
  simp only [whiskerLeft_comp' k, Category.assoc, whiskerLeft_inv_hom_assoc k]
  rw [whisker_exchange_of_even_left_assoc he ((F).mapId Q).inv]
  have ht' := congrArg (· ≫ ex.inv) ht
  simp only [Category.assoc] at ht'
  rw [ht', rightUnitor_naturality_assoc k]
  simp only [Iso.hom_inv_id, Category.comp_id]
  rw [← (F).map₂_rightUnitor x]
  simp only [whiskerLeft_inv_hom_assoc k, Iso.inv_hom_id_assoc]
end OddMath.SKM
