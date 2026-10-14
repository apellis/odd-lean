/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQForwardTriangleGrading

/-!
# Components of the second triangle of `ω_q`

Endpoint comparison for the component at each weight of the second triangle `G_q ⟹ G_q ⋙ ω_q ⋙ G_q ⟹ G_q`.

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
local notation "O" a:max => (⟨⟨a⟩⟩ : B)

def qReverseCounitComparison {a a' : UGr D Sc sy hc} (p : a = a') :
    (G).map (qCounitObj p) ≅ qUnitInvObj (congrArg negWeight p) := by
  subst a'
  exact ((G).mapId (O a)).symm

def qReverseCancel {a a' : UGr D Sc sy hc} (p : a = a') :
    qUnitObj (congrArg negWeight p) ≫ (G).map (qCounitObj p) ≅ 𝟙 ((G).obj (O a)) := by
  subst a'
  exact leftUnitor ((G).map (𝟙 (O a))) ≪≫ ((G).mapId (O a)).symm

/-- Cancellation of the component, not yet modification naturality. -/
def chevalleyQReverseTriangleComponent (b : B) :
    (J).X ((G).obj b) ≫ (G).map ((E).X b) ≅ 𝟙 ((G).obj b) :=
  qReverseCancel (chevQ_negWeight_square b.unop.as).symm

theorem qReverseTransport_obj {a b a' b' : UGr D Sc sy hc}
    (p : a = a') (q : b = b') (f : O a ⟶ O b) :
    (G).map (a := O a') (b := O b') ((chevQEndpointTransport p q).obj f) =
      (qUnitTransport (congrArg negWeight p) (congrArg negWeight q)).obj ((G).map f) := by
  subst a' b'
  rfl

end OddMath.SKM
