/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQForwardTriangleAssembly

/-!
# The first triangle identity of `ω_q`

`chevalleyQForwardTriangleIso`: the first zigzag of `ω_q` is isomorphic to the identity transformation of `ω_q`.

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
local notation "E" => chevalleyQGlobalCounit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "K" => chevalleyQGlobalCounitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)

def qTriangleTransportIso {S T S' T' : TwoSuperfunctor k A B}
    (p : S = S') (q : T = T') {θ ψ : TwoNatTrans S T} (e : θ ≅ ψ) :
    qTriangleTransport p q θ ≅ qTriangleTransport p q ψ := by
  cases p
  cases q
  exact e

theorem qTriangleTransport_vcomp {S T U S' T' U' : TwoSuperfunctor k A B}
    (p : S = S') (q : T = T') (r : U = U') (θ : TwoNatTrans S T) (ψ : TwoNatTrans T U) :
    (qTriangleTransport p q θ).vcomp (qTriangleTransport q r ψ) =
      qTriangleTransport p r (θ.vcomp ψ) := by
  cases p
  cases q
  cases r
  rfl

theorem qTriangleTransport_id {S S' : TwoSuperfunctor k A B} (p : S = S') :
    qTriangleTransport p p (TwoNatTrans.id S) = TwoNatTrans.id S' := by
  cases p
  rfl

def qTriangleWhiskerRightIso {S T U : TwoSuperfunctor k A B}
    {θ θ' : TwoNatTrans S T} (e : θ ≅ θ') (ψ : TwoNatTrans T U) :
    θ.vcomp ψ ≅ θ'.vcomp ψ where
  hom := TwoNatTrans.whiskerRight e.hom ψ
  inv := TwoNatTrans.whiskerRight e.inv ψ
  hom_inv_id := TwoNatTrans.hom_ext fun a => by
    change e.hom.app a ▷ ψ.X a ≫ e.inv.app a ▷ ψ.X a = 𝟙 _
    rw [← comp_whiskerRight (R := k)]
    have h := congrArg (fun α => α.app a) e.hom_inv_id
    change e.hom.app a ≫ e.inv.app a = 𝟙 _ at h
    rw [h, id_whiskerRight (R := k)]
  inv_hom_id := TwoNatTrans.hom_ext fun a => by
    change e.inv.app a ▷ ψ.X a ≫ e.hom.app a ▷ ψ.X a = 𝟙 _
    rw [← comp_whiskerRight (R := k)]
    have h := congrArg (fun α => α.app a) e.inv_hom_id
    change e.inv.app a ≫ e.hom.app a = 𝟙 _ at h
    rw [h, id_whiskerRight (R := k)]

/-- The counit inverse pair, precomposed by F and transported
at its endpoints. -/
def chevalleyQForwardCounitPairIso :
    (chevalleyQForwardCounitInvLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).vcomp
      chevalleyQForwardCounitLeg ≅ TwoNatTrans.id (F) :=
  eqToIso (qTriangleTransport_vcomp (TwoSuperfunctor.comp_id (F)) rfl
    (TwoSuperfunctor.comp_id (F)) (TwoNatTrans.precompose (F) (K))
      (TwoNatTrans.precompose (F) (E))) ≪≫
  qTriangleTransportIso (TwoSuperfunctor.comp_id (F)) (TwoSuperfunctor.comp_id (F))
    ((TwoNatTrans.precomposition (F) _ _).mapIso chevalleyQGlobalCounitInvCompIso) ≪≫
  eqToIso (qTriangleTransport_id (TwoSuperfunctor.comp_id (F)))

/-- The transported composite of the exact J and E cancels to id(F).
No reverse triangle, higher coherence or strict equality is asserted. -/
def chevalleyQForwardTriangleIso :
    chevalleyQForwardZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc) ≅ TwoNatTrans.id (F) :=
  qTriangleWhiskerRightIso chevalleyQForwardUnitComparisonIso chevalleyQForwardCounitLeg ≪≫
    chevalleyQForwardCounitPairIso
end OddMath.SKM
