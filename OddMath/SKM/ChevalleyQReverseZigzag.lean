/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQForwardTriangleGrading

/-!
# The second zigzag of `ω_q`

`chevalleyQReverseZigzag : G_q ⟹ G_q`, the composite of `J ∘ G_q` and `G_q ∘ E`.

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

def qReverseTransport {S T S' T' : TwoSuperfunctor k B A}
    (p : S = S') (q : T = T') (θ : TwoNatTrans S T) : TwoNatTrans S' T' := by
  cases p
  cases q
  exact θ

theorem qReverseTransport_X_heq {S T S' T' : TwoSuperfunctor k B A}
    (p : S = S') (q : T = T') (θ : TwoNatTrans S T) (b : B) :
    HEq ((qReverseTransport p q θ).X b) (θ.X b) := by
  cases p
  cases q
  rfl

theorem qReverseTransport_x_heq {S T S' T' : TwoSuperfunctor k B A}
    (p : S = S') (q : T = T') (θ : TwoNatTrans S T) {a b : B} (f : a ⟶ b) :
    HEq ((qReverseTransport p q θ).x f) (θ.x f) := by
  cases p
  cases q
  rfl

def chevalleyQReverseUnitLeg : TwoNatTrans (G) ((G).comp ((F).comp (G))) :=
  qReverseTransport (TwoSuperfunctor.comp_id (G)) rfl (TwoNatTrans.precompose (G) (J))

def chevalleyQReverseCounitLeg : TwoNatTrans ((G).comp ((F).comp (G))) (G) :=
  qReverseTransport (TwoSuperfunctor.comp_assoc (G) (F) (G)) (TwoSuperfunctor.id_comp (G))
    (TwoNatTrans.postcompose (G) (E))

def chevalleyQReverseZigzag : TwoNatTrans (G) (G) :=
  chevalleyQReverseUnitLeg.vcomp chevalleyQReverseCounitLeg

theorem chevalleyQReverseUnitLeg_X (b : B) :
    (chevalleyQReverseUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).X b =
      (J).X ((G).obj b) := eq_of_heq (qReverseTransport_X_heq _ _ _ b)

theorem chevalleyQReverseCounitLeg_X (b : B) :
    (chevalleyQReverseCounitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).X b =
      (G).map ((E).X b) := eq_of_heq (qReverseTransport_X_heq _ _ _ b)

theorem chevalleyQReverseZigzag_X (b : B) :
    (chevalleyQReverseZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc)).X b =
      (J).X ((G).obj b) ≫ (G).map ((E).X b) := by
  exact congrArg₂ (fun f g => f ≫ g) (chevalleyQReverseUnitLeg_X b)
    (chevalleyQReverseCounitLeg_X b)

theorem chevalleyQReverseUnitLeg_x_heq {a b : B} (f : a ⟶ b) :
    HEq ((chevalleyQReverseUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).x f)
      ((J).x ((G).map f)) :=
  qReverseTransport_x_heq (TwoSuperfunctor.comp_id (G)) rfl
    (TwoNatTrans.precompose (G) (J)) f

end OddMath.SKM
