/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQUnitCancel

/-!
# Components of the first triangle of `ω_q`

The component at each weight of the modification from the zigzag `ω_q ⟹ ω_q ⋙ G_q ⋙ ω_q ⟹ ω_q` to the identity.

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
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "G" => chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "J" => chevalleyQGlobalUnit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "E" => chevalleyQGlobalCounit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "O" a:max => (⟨a⟩ : A)

/-- Equality elimination retains the identity comparison of F. -/
def qForwardCancel {a a' : UGr D Sc sy hc} (p : a = a') :
    (F).map (qUnitObj p) ≫ qCounitObj (congrArg negWeight p) ≅ 𝟙 ((F).obj (O a)) := by
  subst a'
  exact rightUnitor ((F).map (𝟙 (O a))) ≪≫ ((F).mapId (O a)).symm

/-- The component cancels the exact unit and counit. -/
def chevalleyQForwardTriangleComponent (a : A) :
    (F).map ((J).X a) ≫ (E).X ((F).obj a) ≅ 𝟙 ((F).obj a) :=
  qForwardCancel (chevQ_negWeight_square a.as).symm

/-- Map of the inverse reflected counit; no comparison factor is dropped. -/
theorem qUnitHomCounit_inv_image {a b : A} (f : a ⟶ b) :
    (F).map₂ (qUnitHomCounit f).inv =
      eqToHom (qUnitTransport_forward (chevQ_negWeight_square a.as).symm
        (chevQ_negWeight_square b.as).symm f) ≫
      (chevalleyQReverseHomCounit ((F).map f)).inv := by
  have h : (F).map₂Iso (qUnitHomCounit f) =
      chevalleyQReverseHomCounit ((F).map f) ≪≫
        (eqToIso (qUnitTransport_forward (chevQ_negWeight_square a.as).symm
          (chevQ_negWeight_square b.as).symm f)).symm :=
    Iso.ext (qUnitHomCounit_image f)
  exact congrArg Iso.inv h
end OddMath.SKM
