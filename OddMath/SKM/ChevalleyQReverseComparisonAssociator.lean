/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseTransportAssociator

/-!
# Associativity axiom for `G_q`

The associativity axiom of `G_q`, reflected through `ω_q`.

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

/-- The associator law for the exact reverse composition comparisons. -/
theorem chevalleyQReverse_associator {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (chevalleyQReverseHom a b).obj f ◁ (chevalleyQReverseMapComp g h).hom ≫
      (chevalleyQReverseMapComp f (g ≫ h)).hom ≫
      (chevalleyQReverseHom a d).map (associator f g h).inv =
    (associator ((chevalleyQReverseHom a b).obj f) ((chevalleyQReverseHom b c).obj g)
      ((chevalleyQReverseHom c d).obj h)).inv ≫
      (chevalleyQReverseMapComp f g).hom ▷ (chevalleyQReverseHom c d).obj h ≫
      (chevalleyQReverseMapComp (f ≫ g) h).hom := by
  let P := chevalleyQReverseObj a
  let Q := chevalleyQReverseObj b
  let S := chevalleyQReverseObj c
  let T := chevalleyQReverseObj d
  let x : P ⟶ Q := (chevalleyQReverseHom a b).obj f
  let y : Q ⟶ S := (chevalleyQReverseHom b c).obj g
  let z : S ⟶ T := (chevalleyQReverseHom c d).obj h
  let u : P ⟶ S := (chevalleyQReverseHom a c).obj (f ≫ g)
  let v : Q ⟶ T := (chevalleyQReverseHom b d).obj (g ≫ h)
  let l : P ⟶ T := (chevalleyQReverseHom a d).obj (f ≫ g ≫ h)
  let r : P ⟶ T := (chevalleyQReverseHom a d).obj ((f ≫ g) ≫ h)
  let ca : l ⟶ r := (chevalleyQReverseHom a d).map (associator f g h).inv
  let cxy : x ≫ y ≅ u := chevalleyQReverseMapComp f g
  let cyz : y ≫ z ≅ v := chevalleyQReverseMapComp g h
  let cxv : x ≫ v ≅ l := chevalleyQReverseMapComp f (g ≫ h)
  let cuz : u ≫ z ≅ r := chevalleyQReverseMapComp (f ≫ g) h
  let tx : (F).obj P ⟶ (F).obj Q := (chevalleyQReverseTransport a b).obj f
  let ty : (F).obj Q ⟶ (F).obj S := (chevalleyQReverseTransport b c).obj g
  let tz : (F).obj S ⟶ (F).obj T := (chevalleyQReverseTransport c d).obj h
  let tu : (F).obj P ⟶ (F).obj S := (chevalleyQReverseTransport a c).obj (f ≫ g)
  let tv : (F).obj Q ⟶ (F).obj T := (chevalleyQReverseTransport b d).obj (g ≫ h)
  let tl : (F).obj P ⟶ (F).obj T := (chevalleyQReverseTransport a d).obj (f ≫ g ≫ h)
  let tr : (F).obj P ⟶ (F).obj T := (chevalleyQReverseTransport a d).obj ((f ≫ g) ≫ h)
  let ex : (F).map x ≅ tx := chevalleyQReverseHomCounit f
  let ey : (F).map y ≅ ty := chevalleyQReverseHomCounit g
  let ez : (F).map z ≅ tz := chevalleyQReverseHomCounit h
  let eu : (F).map u ≅ tu := chevalleyQReverseHomCounit (f ≫ g)
  let ev : (F).map v ≅ tv := chevalleyQReverseHomCounit (g ≫ h)
  let el : (F).map l ≅ tl := chevalleyQReverseHomCounit (f ≫ g ≫ h)
  let er : (F).map r ≅ tr := chevalleyQReverseHomCounit ((f ≫ g) ≫ h)
  let txy : tx ≫ ty ≅ tu := (eqToIso (chevalleyQReverseTransport_comp f g)).symm
  let tyz : ty ≫ tz ≅ tv := (eqToIso (chevalleyQReverseTransport_comp g h)).symm
  let txv : tx ≫ tv ≅ tl := (eqToIso (chevalleyQReverseTransport_comp f (g ≫ h))).symm
  let tuz : tu ≫ tz ≅ tr := (eqToIso (chevalleyQReverseTransport_comp (f ≫ g) h)).symm
  let ta : tl ⟶ tr := (chevalleyQReverseTransport a d).map (associator f g h).inv
  have hca : (F).map₂ ca = el.hom ≫ ta ≫ er.inv :=
    chevalleyQReverseHom_map_image (associator f g h).inv
  have hxy : (F).map₂ cxy.hom = ((F).mapComp x y).inv ≫
      ex.hom ▷ (F).map y ≫ tx ◁ ey.hom ≫ txy.hom ≫ eu.inv :=
    chevalleyQReverseMapComp_image f g
  have hyz : (F).map₂ cyz.hom = ((F).mapComp y z).inv ≫
      ey.hom ▷ (F).map z ≫ ty ◁ ez.hom ≫ tyz.hom ≫ ev.inv :=
    chevalleyQReverseMapComp_image g h
  have hxv : (F).map₂ cxv.hom = ((F).mapComp x v).inv ≫
      ex.hom ▷ (F).map v ≫ tx ◁ ev.hom ≫ txv.hom ≫ el.inv :=
    chevalleyQReverseMapComp_image f (g ≫ h)
  have huz : (F).map₂ cuz.hom = ((F).mapComp u z).inv ≫
      eu.hom ▷ (F).map z ≫ tu ◁ ez.hom ≫ tuz.hom ≫ er.inv :=
    chevalleyQReverseMapComp_image (f ≫ g) h
  have ht : tx ◁ tyz.hom ≫ txv.hom ≫ ta =
      (associator tx ty tz).inv ≫ txy.hom ▷ tz ≫ tuz.hom :=
    chevQEndpointTransport_associator (chevQ_negWeight_square a.unop.as).symm
      (chevQ_negWeight_square b.unop.as).symm (chevQ_negWeight_square c.unop.as).symm
      (chevQ_negWeight_square d.unop.as).symm f g h
  have hex : ex.hom ∈ parity (R := k) _ _ 0 := chevalleyQReverseHomCounit_even f
  have het : txy.hom ∈ parity (R := k) _ _ 0 :=
    eqToHom_mem (R := k) (C := (F).obj P ⟶ (F).obj S)
      (chevalleyQReverseTransport_comp f g).symm
  have hwL : (F).map₂ (x ◁ cyz.hom) = ((F).mapComp x (y ≫ z)).inv ≫
      (F).map x ◁ (F).map₂ cyz.hom ≫ ((F).mapComp x v).hom := by
    rw [(F).mapComp_naturality_right, Iso.inv_hom_id_assoc]
  have hwR : (F).map₂ (cxy.hom ▷ z) = ((F).mapComp (x ≫ y) z).inv ≫
      (F).map₂ cxy.hom ▷ (F).map z ≫ ((F).mapComp u z).hom := by
    rw [(F).mapComp_naturality_left, Iso.inv_hom_id_assoc]
  have ha : (F).map₂ (associator x y z).inv =
      ((F).mapComp x (y ≫ z)).inv ≫ (F).map x ◁ ((F).mapComp y z).inv ≫
      (associator ((F).map x) ((F).map y) ((F).map z)).inv ≫
      ((F).mapComp x y).hom ▷ (F).map z ≫ ((F).mapComp (x ≫ y) z).hom := by
    rw [← (F).map₂_associator]
    simp only [whiskerLeft_inv_hom_assoc k, Iso.inv_hom_id_assoc]
  apply (chevQHom (negWeight a.unop.as) (negWeight d.unop.as)).map_injective
  change (F).map₂ (x ◁ cyz.hom ≫ cxv.hom ≫ ca) =
    (F).map₂ ((associator x y z).inv ≫ cxy.hom ▷ z ≫ cuz.hom)
  simp only [(F).map₂_comp]
  rw [hwL, hwR, hxv, huz, hca, ha]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [← whisker_exchange_of_even_left_assoc hex]
  rw [hxy, hyz]
  simp only [whiskerLeft_comp' k, comp_whiskerRight' k, Category.assoc,
    whiskerLeft_inv_hom_assoc k, inv_hom_whiskerRight_assoc k,
    hom_inv_whiskerRight_assoc k]
  rw [whisker_exchange_of_even_left_assoc hex ((F).mapComp y z).inv,
    whisker_exchange_of_even_left_assoc het ez.hom, reassoc_of% ht,
    associator_inv_naturality_right_assoc k, associator_inv_naturality_middle_assoc k,
    associator_inv_naturality_left_assoc k]
end OddMath.SKM
