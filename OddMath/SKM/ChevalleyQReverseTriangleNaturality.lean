/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseTriangleComparison

/-!
# Naturality of the second triangle of `ω_q`

The components of the second triangle form a modification.

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
local notation "B" => TwoSOp k A
local notation "G" => chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "O" a:max => (⟨⟨a⟩⟩ : B)

theorem qReverseCounitComparison_naturality
    {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b')
    (f : O a ⟶ O b) (s : O a' ⟶ O b')
    (e : s ≅ (chevQEndpointTransport p q).obj f)
    (d : (G).map s ≅ (qUnitTransport (congrArg negWeight p)
      (congrArg negWeight q)).obj ((G).map f))
    (h : (G).map₂ e.hom ≫ eqToHom (qReverseTransport_obj p q f) = d.hom) :
    ((G).mapComp s (qCounitObj q)).hom ≫ (G).map₂ (qCounitCell p q f s e).hom ≫
      ((G).mapComp (qCounitObj p) f).inv ≫ (qReverseCounitComparison p).hom ▷ (G).map f =
    (G).map s ◁ (qReverseCounitComparison q).hom ≫
      (qUnitInvCell (congrArg negWeight p) (congrArg negWeight q)
        ((G).map f) ((G).map s) d).hom := by
  subst a' b'
  change s ≅ f at e
  change (G).map s ≅ (G).map f at d
  change (G).map₂ e.hom ≫ 𝟙 _ = d.hom at h
  rw [Category.comp_id] at h
  change ((G).mapComp s (𝟙 (O b))).hom ≫
    (G).map₂ ((rightUnitor s).hom ≫ e.hom ≫ (leftUnitor f).inv) ≫
    ((G).mapComp (𝟙 (O a)) f).inv ≫ ((G).mapId (O a)).inv ▷ (G).map f =
    (G).map s ◁ ((G).mapId (O b)).inv ≫
      (rightUnitor ((G).map s)).hom ≫ d.hom ≫ (leftUnitor ((G).map f)).inv
  have hr : ((G).mapComp s (𝟙 (O b))).hom ≫ (G).map₂ (rightUnitor s).hom =
      (G).map s ◁ ((G).mapId (O b)).inv ≫ (rightUnitor ((G).map s)).hom := by
    rw [← cancel_epi (whiskerLeftIso (R := k) ((G).map s) ((G).mapId (O b))).hom]
    simp only [whiskerLeftIso_hom]
    rw [(G).map₂_rightUnitor, ← Category.assoc, whiskerLeft_hom_inv k, Category.id_comp]
  have hl : (G).map₂ (leftUnitor f).inv ≫ ((G).mapComp (𝟙 (O a)) f).inv ≫
      ((G).mapId (O a)).inv ▷ (G).map f = (leftUnitor ((G).map f)).inv := by
    apply (cancel_mono (leftUnitor ((G).map f)).hom).mp
    rw [Category.assoc, Category.assoc, ← (G).map₂_leftUnitor f]
    simp only [inv_hom_whiskerRight_assoc k, Iso.inv_hom_id_assoc,
      ← (G).map₂_comp, Iso.inv_hom_id, (G).map₂_id]
    rw [(G).map₂_leftUnitor, Iso.inv_hom_id]
  rw [(G).map₂_comp, (G).map₂_comp, h]
  simp only [Category.assoc]
  rw [reassoc_of% hr, hl]

end OddMath.SKM
