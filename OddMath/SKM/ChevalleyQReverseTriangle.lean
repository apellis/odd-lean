/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseTriangleAssembly

/-!
# The second triangle identity of `ω_q`

`chevalleyQReverseTriangleIso`: the second zigzag of `ω_q` is isomorphic to the identity transformation of `G_q`.

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
local notation "J" => chevalleyQGlobalUnit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "K" => chevalleyQGlobalUnitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)

def qReverseTransportIso {S T S' T' : TwoSuperfunctor k B A}
    (p : S = S') (q : T = T') {θ ψ : TwoNatTrans S T} (e : θ ≅ ψ) :
    qReverseTransport p q θ ≅ qReverseTransport p q ψ := by
  cases p
  cases q
  exact e

theorem qReverseTransport_vcomp {S T U S' T' U' : TwoSuperfunctor k B A}
    (p : S = S') (q : T = T') (r : U = U') (θ : TwoNatTrans S T) (ψ : TwoNatTrans T U) :
    (qReverseTransport p q θ).vcomp (qReverseTransport q r ψ) =
      qReverseTransport p r (θ.vcomp ψ) := by
  cases p
  cases q
  cases r
  rfl

theorem qReverseTransport_id {S S' : TwoSuperfunctor k B A} (p : S = S') :
    qReverseTransport p p (TwoNatTrans.id S) = TwoNatTrans.id S' := by
  cases p
  rfl

def qReverseWhiskerLeftIso {S T U : TwoSuperfunctor k B A}
    (θ : TwoNatTrans S T) {ψ ψ' : TwoNatTrans T U} (e : ψ ≅ ψ') :
    θ.vcomp ψ ≅ θ.vcomp ψ' where
  hom := TwoNatTrans.whiskerLeft θ e.hom
  inv := TwoNatTrans.whiskerLeft θ e.inv
  hom_inv_id := TwoNatTrans.hom_ext fun a => by
    change θ.X a ◁ e.hom.app a ≫ θ.X a ◁ e.inv.app a = 𝟙 _
    rw [← whiskerLeft_comp (R := k)]
    have h := congrArg (fun α => α.app a) e.hom_inv_id
    change e.hom.app a ≫ e.inv.app a = 𝟙 _ at h
    rw [h, whiskerLeft_id (R := k)]
  inv_hom_id := TwoNatTrans.hom_ext fun a => by
    change θ.X a ◁ e.inv.app a ≫ θ.X a ◁ e.hom.app a = 𝟙 _
    rw [← whiskerLeft_comp (R := k)]
    have h := congrArg (fun α => α.app a) e.inv_hom_id
    change e.inv.app a ≫ e.hom.app a = 𝟙 _ at h
    rw [h, whiskerLeft_id (R := k)]

def chevalleyQReverseUnitPairIso :
    (chevalleyQReverseUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).vcomp
      chevalleyQReverseUnitInvLeg ≅ TwoNatTrans.id (G) :=
  eqToIso (qReverseTransport_vcomp (TwoSuperfunctor.comp_id (G)) rfl
    (TwoSuperfunctor.comp_id (G)) (TwoNatTrans.precompose (G) (J))
      (TwoNatTrans.precompose (G) (K))) ≪≫
  qReverseTransportIso (TwoSuperfunctor.comp_id (G)) (TwoSuperfunctor.comp_id (G))
    ((TwoNatTrans.precomposition (G) _ _).mapIso chevalleyQGlobalUnitCompIso) ≪≫
  eqToIso (qReverseTransport_id (TwoSuperfunctor.comp_id (G)))

/-- The J precomposed by G followed by the E postcomposed by G
is isomorphic to id(G) in the modification category. -/
def chevalleyQReverseTriangleIso :
    chevalleyQReverseZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc) ≅ TwoNatTrans.id (G) :=
  qReverseWhiskerLeftIso chevalleyQReverseUnitLeg chevalleyQReverseCounitComparisonIso ≪≫
    chevalleyQReverseUnitPairIso

end OddMath.SKM
