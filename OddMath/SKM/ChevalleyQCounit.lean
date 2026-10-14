/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQCounitTransport

/-!
# The counit of `ω_q`

`chevalleyQGlobalCounit : G_q ⋙ ω_q ⟹ 1`, a strong graded 2-natural transformation on `𝔘_q(𝔤)^{sop}`.

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

/-- The composite comparison followed by the hom counit. -/
theorem qGlobalCounit_comp_image {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    ((H).mapComp f g).hom ≫ (chevalleyQReverseHomCounit (f ≫ g)).hom =
      (chevalleyQReverseHomCounit f).hom ▷ (H).map g ≫
      (show (H).obj a ⟶ (H).obj b from (chevalleyQReverseTransport a b).obj f) ◁
        (chevalleyQReverseHomCounit g).hom ≫
      eqToHom (chevalleyQReverseTransport_comp f g).symm := by
  let x : (G).obj a ⟶ (G).obj b := (G).map f
  let y : (G).obj b ⟶ (G).obj c := (G).map g
  let z : (G).obj a ⟶ (G).obj c := (G).map (f ≫ g)
  let tx : (F).obj ((G).obj a) ⟶ (F).obj ((G).obj b) :=
    (chevalleyQReverseTransport a b).obj f
  let ty : (F).obj ((G).obj b) ⟶ (F).obj ((G).obj c) :=
    (chevalleyQReverseTransport b c).obj g
  let tz : (F).obj ((G).obj a) ⟶ (F).obj ((G).obj c) :=
    (chevalleyQReverseTransport a c).obj (f ≫ g)
  let ex : (F).map x ≅ tx := chevalleyQReverseHomCounit f
  let ey : (F).map y ≅ ty := chevalleyQReverseHomCounit g
  let ez : (F).map z ≅ tz := chevalleyQReverseHomCounit (f ≫ g)
  let t : tx ≫ ty ≅ tz := (eqToIso (chevalleyQReverseTransport_comp f g)).symm
  let κ : x ≫ y ≅ z := chevalleyQReverseMapComp f g
  have h : (F).map₂ κ.hom = ((F).mapComp x y).inv ≫
      ex.hom ▷ (F).map y ≫ tx ◁ ey.hom ≫ t.hom ≫ ez.inv :=
    chevalleyQReverseMapComp_image f g
  change (((F).mapComp x y).hom ≫ (F).map₂ κ.hom) ≫ ez.hom =
    ex.hom ▷ (F).map y ≫ tx ◁ ey.hom ≫ t.hom
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The composite unit comparison cancels the hom counit. -/
theorem qGlobalCounit_id_image (a : B) :
    ((H).mapId a).hom ≫ (chevalleyQReverseHomCounit (𝟙 a)).hom =
      eqToHom (chevalleyQReverseTransport_id a).symm := by
  let s : (G).obj a ⟶ (G).obj a := (G).map (𝟙 a)
  let t : (F).obj ((G).obj a) ⟶ (F).obj ((G).obj a) :=
    (chevalleyQReverseTransport a a).obj (𝟙 a)
  let e : (F).map s ≅ t := chevalleyQReverseHomCounit (𝟙 a)
  let i : 𝟙 ((G).obj a) ≅ s := chevalleyQReverseMapId a
  let j : 𝟙 ((F).obj ((G).obj a)) ≅ t :=
    (eqToIso (chevalleyQReverseTransport_id a)).symm
  have h : (F).map₂ i.hom = ((F).mapId ((G).obj a)).inv ≫ j.hom ≫ e.inv :=
    chevalleyQReverseMapId_image a
  change (((F).mapId ((G).obj a)).hom ≫ (F).map₂ i.hom) ≫ e.hom = j.hom
  rw [h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The equality of double-negated objects, as a 1-morphism. -/
def chevalleyQGlobalCounitObj (a : B) : (H).obj a ⟶ a :=
  qCounitObj (chevQ_negWeight_square a.unop.as).symm

/-- Exact counit component with the unitors and endpoint equality data. -/
def chevalleyQGlobalCounitCell {a b : B} (f : a ⟶ b) :
    (H).map f ≫ chevalleyQGlobalCounitObj b ≅ chevalleyQGlobalCounitObj a ≫ f :=
  qCounitCell (chevQ_negWeight_square a.unop.as).symm
    (chevQ_negWeight_square b.unop.as).symm f ((H).map f) (chevalleyQReverseHomCounit f)

/-- Global counit from the forward-after-reverse composite to the identity. -/
def chevalleyQGlobalCounit : TwoNatTrans (H) (TwoSuperfunctor.id k (B)) where
  X := chevalleyQGlobalCounitObj
  x f := (chevalleyQGlobalCounitCell f).hom
  x_mem f := qCounitCell_even _ _ _ _ _ (chevalleyQReverseHomCounit_even f)
  naturality η := qCounitCell_naturality _ _ _ _ η ((H).map₂ η)
    (chevalleyQReverseHomCounit_naturality η)
  x_comp f g := qCounitCell_comp _ _ _ f g ((H).map f) ((H).map g) ((H).map (f ≫ g))
    (chevalleyQReverseHomCounit f) (chevalleyQReverseHomCounit g)
    (chevalleyQReverseHomCounit (f ≫ g)) ((H).mapComp f g).hom
    (chevalleyQReverseHomCounit_even f) (qGlobalCounit_comp_image f g)
  x_id a := qCounitCell_id _ ((H).map (𝟙 a)) (chevalleyQReverseHomCounit (𝟙 a))
    ((H).mapId a).hom (qGlobalCounit_id_image a)

/-- Every global counit 2-cell is invertible, not merely a local equivalence assertion. -/
theorem chevalleyQGlobalCounit_isStrong :
    (chevalleyQGlobalCounit (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).IsStrong :=
  fun f => inferInstanceAs (IsIso (chevalleyQGlobalCounitCell f).hom)

/-- The exact global counit components have integer degree zero. -/
theorem chevalleyQGlobalCounit_isGraded :
    (chevalleyQGlobalCounit (D := D) (Sc := Sc) (sy := sy) (hc := hc) (k := k)).IsGraded :=
  fun f => qCounitCell_degree _ _ _ _ _ (chevalleyQReverseHomCounit_degree f)
end OddMath.SKM
