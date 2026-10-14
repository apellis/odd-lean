/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseTransportNaturality

/-!
# Naturality of the comparisons of `G_q`

Naturality of the composition comparison of `G_q` in both variables, reflected through the faithful hom functors of `ω_q`.

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

/-- The forward image of the reverse map is counit conjugation. -/
theorem chevalleyQReverseHom_map_image {a b : B} {f f' : a ⟶ b} (η : f ⟶ f') :
    (F).map₂ ((chevalleyQReverseHom a b).map η) =
      (chevalleyQReverseHomCounit f).hom ≫ (chevalleyQReverseTransport a b).map η ≫
        (chevalleyQReverseHomCounit f').inv := by
  exact ((Iso.eq_comp_inv (C := (F).obj (chevalleyQReverseObj a) ⟶
    (F).obj (chevalleyQReverseObj b)) (chevalleyQReverseHomCounit f')).2
      (chevalleyQReverseHomCounit_naturality η)).trans (Category.assoc _ _ _)

/-- Left naturality on arbitrary morphisms for the exact comparison. -/
theorem chevalleyQReverseMapComp_naturality_left {a b c : B} {f f' : a ⟶ b}
    (η : f ⟶ f') (g : b ⟶ c) :
    (chevalleyQReverseHom a b).map η ▷ (chevalleyQReverseHom b c).obj g ≫
      (chevalleyQReverseMapComp f' g).hom =
    (chevalleyQReverseMapComp f g).hom ≫ (chevalleyQReverseHom a c).map (η ▷ g) := by
  let P := chevalleyQReverseObj a
  let Q := chevalleyQReverseObj b
  let S := chevalleyQReverseObj c
  let x : P ⟶ Q := (chevalleyQReverseHom a b).obj f
  let x' : P ⟶ Q := (chevalleyQReverseHom a b).obj f'
  let y : Q ⟶ S := (chevalleyQReverseHom b c).obj g
  let z : P ⟶ S := (chevalleyQReverseHom a c).obj (f ≫ g)
  let z' : P ⟶ S := (chevalleyQReverseHom a c).obj (f' ≫ g)
  let u : x ⟶ x' := (chevalleyQReverseHom a b).map η
  let v : z ⟶ z' := (chevalleyQReverseHom a c).map (η ▷ g)
  let cs : x ≫ y ≅ z := chevalleyQReverseMapComp f g
  let ct : x' ≫ y ≅ z' := chevalleyQReverseMapComp f' g
  let tx : (F).obj P ⟶ (F).obj Q := (chevalleyQReverseTransport a b).obj f
  let tx' : (F).obj P ⟶ (F).obj Q := (chevalleyQReverseTransport a b).obj f'
  let ty : (F).obj Q ⟶ (F).obj S := (chevalleyQReverseTransport b c).obj g
  let tz : (F).obj P ⟶ (F).obj S := (chevalleyQReverseTransport a c).obj (f ≫ g)
  let tz' : (F).obj P ⟶ (F).obj S := (chevalleyQReverseTransport a c).obj (f' ≫ g)
  let ex : (F).map x ≅ tx := chevalleyQReverseHomCounit f
  let ex' : (F).map x' ≅ tx' := chevalleyQReverseHomCounit f'
  let ey : (F).map y ≅ ty := chevalleyQReverseHomCounit g
  let ez : (F).map z ≅ tz := chevalleyQReverseHomCounit (f ≫ g)
  let ez' : (F).map z' ≅ tz' := chevalleyQReverseHomCounit (f' ≫ g)
  let ts : tx ≫ ty ≅ tz := (eqToIso (chevalleyQReverseTransport_comp f g)).symm
  let tt : tx' ≫ ty ≅ tz' := (eqToIso (chevalleyQReverseTransport_comp f' g)).symm
  let tu : tx ⟶ tx' := (chevalleyQReverseTransport a b).map η
  let tv : tz ⟶ tz' := (chevalleyQReverseTransport a c).map (η ▷ g)
  have hu : (F).map₂ u = ex.hom ≫ tu ≫ ex'.inv := chevalleyQReverseHom_map_image η
  have hv : (F).map₂ v = ez.hom ≫ tv ≫ ez'.inv :=
    chevalleyQReverseHom_map_image (η ▷ g)
  have hs : (F).map₂ cs.hom = ((F).mapComp x y).inv ≫
      ex.hom ▷ (F).map y ≫ tx ◁ ey.hom ≫ ts.hom ≫ ez.inv :=
    chevalleyQReverseMapComp_image f g
  have ht : (F).map₂ ct.hom = ((F).mapComp x' y).inv ≫
      ex'.hom ▷ (F).map y ≫ tx' ◁ ey.hom ≫ tt.hom ≫ ez'.inv :=
    chevalleyQReverseMapComp_image f' g
  have htNat : tu ▷ ty ≫ tt.hom = ts.hom ≫ tv :=
    chevalleyQReverseTransport_comp_left η g
  have he : ey.hom ∈ parity (R := k) _ _ 0 := chevalleyQReverseHomCounit_even g
  have hw : (F).map₂ (u ▷ y) = ((F).mapComp x y).inv ≫
      (F).map₂ u ▷ (F).map y ≫ ((F).mapComp x' y).hom := by
    rw [(F).mapComp_naturality_left, Iso.inv_hom_id_assoc]
  apply (chevQHom (negWeight a.unop.as) (negWeight c.unop.as)).map_injective
  change (F).map₂ (u ▷ y ≫ ct.hom) = (F).map₂ (cs.hom ≫ v)
  rw [(F).map₂_comp, (F).map₂_comp, hw, hs, ht, hu, hv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    comp_whiskerRight' k, inv_hom_whiskerRight_assoc k]
  rw [whisker_exchange_of_even_right_assoc tu he]
  have htNat' := congrArg (· ≫ ez'.inv) htNat
  simp only [Category.assoc] at htNat'
  rw [htNat']
/-- Right naturality on arbitrary morphisms for the exact comparison. -/
theorem chevalleyQReverseMapComp_naturality_right {a b c : B} (f : a ⟶ b)
    {g g' : b ⟶ c} (η : g ⟶ g') :
    (chevalleyQReverseHom a b).obj f ◁ (chevalleyQReverseHom b c).map η ≫
      (chevalleyQReverseMapComp f g').hom =
    (chevalleyQReverseMapComp f g).hom ≫ (chevalleyQReverseHom a c).map (f ◁ η) := by
  let P := chevalleyQReverseObj a
  let Q := chevalleyQReverseObj b
  let S := chevalleyQReverseObj c
  let x : P ⟶ Q := (chevalleyQReverseHom a b).obj f
  let y : Q ⟶ S := (chevalleyQReverseHom b c).obj g
  let y' : Q ⟶ S := (chevalleyQReverseHom b c).obj g'
  let z : P ⟶ S := (chevalleyQReverseHom a c).obj (f ≫ g)
  let z' : P ⟶ S := (chevalleyQReverseHom a c).obj (f ≫ g')
  let u : y ⟶ y' := (chevalleyQReverseHom b c).map η
  let v : z ⟶ z' := (chevalleyQReverseHom a c).map (f ◁ η)
  let cs : x ≫ y ≅ z := chevalleyQReverseMapComp f g
  let ct : x ≫ y' ≅ z' := chevalleyQReverseMapComp f g'
  let tx : (F).obj P ⟶ (F).obj Q := (chevalleyQReverseTransport a b).obj f
  let ty : (F).obj Q ⟶ (F).obj S := (chevalleyQReverseTransport b c).obj g
  let ty' : (F).obj Q ⟶ (F).obj S := (chevalleyQReverseTransport b c).obj g'
  let tz : (F).obj P ⟶ (F).obj S := (chevalleyQReverseTransport a c).obj (f ≫ g)
  let tz' : (F).obj P ⟶ (F).obj S := (chevalleyQReverseTransport a c).obj (f ≫ g')
  let ex : (F).map x ≅ tx := chevalleyQReverseHomCounit f
  let ey : (F).map y ≅ ty := chevalleyQReverseHomCounit g
  let ey' : (F).map y' ≅ ty' := chevalleyQReverseHomCounit g'
  let ez : (F).map z ≅ tz := chevalleyQReverseHomCounit (f ≫ g)
  let ez' : (F).map z' ≅ tz' := chevalleyQReverseHomCounit (f ≫ g')
  let ts : tx ≫ ty ≅ tz := (eqToIso (chevalleyQReverseTransport_comp f g)).symm
  let tt : tx ≫ ty' ≅ tz' := (eqToIso (chevalleyQReverseTransport_comp f g')).symm
  let tu : ty ⟶ ty' := (chevalleyQReverseTransport b c).map η
  let tv : tz ⟶ tz' := (chevalleyQReverseTransport a c).map (f ◁ η)
  have hu : (F).map₂ u = ey.hom ≫ tu ≫ ey'.inv := chevalleyQReverseHom_map_image η
  have hv : (F).map₂ v = ez.hom ≫ tv ≫ ez'.inv :=
    chevalleyQReverseHom_map_image (f ◁ η)
  have hs : (F).map₂ cs.hom = ((F).mapComp x y).inv ≫
      ex.hom ▷ (F).map y ≫ tx ◁ ey.hom ≫ ts.hom ≫ ez.inv :=
    chevalleyQReverseMapComp_image f g
  have ht : (F).map₂ ct.hom = ((F).mapComp x y').inv ≫
      ex.hom ▷ (F).map y' ≫ tx ◁ ey'.hom ≫ tt.hom ≫ ez'.inv :=
    chevalleyQReverseMapComp_image f g'
  have htNat : tx ◁ tu ≫ tt.hom = ts.hom ≫ tv :=
    chevalleyQReverseTransport_comp_right f η
  have he : ex.hom ∈ parity (R := k) _ _ 0 := chevalleyQReverseHomCounit_even f
  have hw : (F).map₂ (x ◁ u) = ((F).mapComp x y).inv ≫
      (F).map x ◁ (F).map₂ u ≫ ((F).mapComp x y').hom := by
    rw [(F).mapComp_naturality_right, Iso.inv_hom_id_assoc]
  apply (chevQHom (negWeight a.unop.as) (negWeight c.unop.as)).map_injective
  change (F).map₂ (x ◁ u ≫ ct.hom) = (F).map₂ (cs.hom ≫ v)
  rw [(F).map₂_comp, (F).map₂_comp, hw, hs, ht, hv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [← whisker_exchange_of_even_left_assoc he]
  rw [hu]
  simp only [whiskerLeft_comp' k, Category.assoc, whiskerLeft_inv_hom_assoc k]
  have htNat' := congrArg (· ≫ ez'.inv) htNat
  simp only [Category.assoc] at htNat'
  rw [htNat']
end OddMath.SKM
