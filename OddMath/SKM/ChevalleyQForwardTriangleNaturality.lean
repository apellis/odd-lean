/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQForwardTriangleComponent

/-!
# Naturality of the first triangle of `ω_q`

The components of the first triangle form a modification.

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
local notation "O" a:max => (⟨a⟩ : A)

def qForwardUnitComparison {a a' : UGr D Sc sy hc} (p : a = a') :
    (F).map (qUnitObj p) ≅ qCounitInvObj (congrArg negWeight p) := by
  subst a'
  exact ((F).mapId (O a)).symm

/-- The image of the unit cell agrees with the inverse counit cell
under the identity comparisons; both compositors are retained. -/
theorem qForwardUnitComparison_naturality
    {a b a' b' : UGr D Sc sy hc} (p : a = a') (q : b = b')
    (f : O a ⟶ O b) (s : O a' ⟶ O b')
    (e : s ≅ (qUnitTransport p q).obj f)
    (d : (F).map s ≅ (chevQEndpointTransport (congrArg negWeight p)
      (congrArg negWeight q)).obj ((F).map f))
    (h : (F).map₂ e.hom = d.hom ≫ eqToHom (qUnitTransport_forward p q f).symm) :
    ((F).mapComp f (qUnitObj q)).hom ≫ (F).map₂ (qUnitCell p q f s e).hom ≫
      ((F).mapComp (qUnitObj p) s).inv ≫ (qForwardUnitComparison p).hom ▷ (F).map s =
    (F).map f ◁ (qForwardUnitComparison q).hom ≫
      (qCounitInvCell (congrArg negWeight p) (congrArg negWeight q)
        ((F).map f) ((F).map s) d).hom := by
  subst a' b'
  change s ≅ f at e
  change (F).map s ≅ (F).map f at d
  change (F).map₂ e.hom = d.hom ≫ 𝟙 _ at h
  rw [Category.comp_id] at h
  have hi : (F).map₂ e.inv = d.inv :=
    congrArg Iso.inv (show (F).map₂Iso e = d from Iso.ext h)
  change ((F).mapComp f (𝟙 (O b))).hom ≫
    (F).map₂ ((rightUnitor f).hom ≫ e.inv ≫ (leftUnitor s).inv) ≫
    ((F).mapComp (𝟙 (O a)) s).inv ≫ ((F).mapId (O a)).inv ▷ (F).map s =
    (F).map f ◁ ((F).mapId (O b)).inv ≫
      (rightUnitor ((F).map f)).hom ≫ d.inv ≫ (leftUnitor ((F).map s)).inv
  have hr : ((F).mapComp f (𝟙 (O b))).hom ≫ (F).map₂ (rightUnitor f).hom =
      (F).map f ◁ ((F).mapId (O b)).inv ≫ (rightUnitor ((F).map f)).hom := by
    rw [← cancel_epi (whiskerLeftIso (R := k) ((F).map f) ((F).mapId (O b))).hom]
    simp only [whiskerLeftIso_hom]
    rw [(F).map₂_rightUnitor, ← Category.assoc, whiskerLeft_hom_inv k, Category.id_comp]
  have hl : (F).map₂ (leftUnitor s).inv ≫ ((F).mapComp (𝟙 (O a)) s).inv ≫
      ((F).mapId (O a)).inv ▷ (F).map s = (leftUnitor ((F).map s)).inv := by
    apply (cancel_mono (leftUnitor ((F).map s)).hom).mp
    rw [Category.assoc, Category.assoc, ← (F).map₂_leftUnitor s]
    simp only [inv_hom_whiskerRight_assoc k, Iso.inv_hom_id_assoc,
      ← (F).map₂_comp, Iso.inv_hom_id, (F).map₂_id]
    rw [(F).map₂_leftUnitor, Iso.inv_hom_id]
  rw [(F).map₂_comp, (F).map₂_comp, hi]
  simp only [Category.assoc]
  rw [reassoc_of% hr, hl]
end OddMath.SKM
