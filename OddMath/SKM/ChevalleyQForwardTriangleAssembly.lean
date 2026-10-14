/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQForwardZigzag
import OddMath.SKM.ChevalleyQForwardTriangleNaturality

/-!
# Assembly of the first triangle of `ω_q`

An isomorphism of transformations from componentwise data. Defines the leg `L ∘ ω_q` (`L` the inverse counit) and an isomorphism `chevalleyQForwardUnitComparisonIso` from the unit leg `ω_q ∘ J` to it.

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
local notation "K" => chevalleyQGlobalCounitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)

/-- Assemble a component isomorphism after proved equality transports of the
component families and cells. This helper is confined to the A/B pair. -/
def qTriangleIsoOfComponents {S T : TwoSuperfunctor k A B} (θ ψ : TwoNatTrans S T)
    (U V : ∀ a, S.obj a ⟶ T.obj a)
    (x : ∀ {a b : A} (f : a ⟶ b), S.map f ≫ U b ⟶ U a ≫ T.map f)
    (y : ∀ {a b : A} (f : a ⟶ b), S.map f ≫ V b ⟶ V a ≫ T.map f)
    (hU : θ.X = U) (hV : ψ.X = V)
    (hx : ∀ {a b : A} (f : a ⟶ b), HEq (θ.x f) (x f))
    (hy : ∀ {a b : A} (f : a ⟶ b), HEq (ψ.x f) (y f))
    (e : ∀ a, U a ≅ V a)
    (hn : ∀ {a b : A} (f : a ⟶ b),
      x f ≫ (e a).hom ▷ T.map f = S.map f ◁ (e b).hom ≫ y f) : θ ≅ ψ := by
  subst U V
  have nat {a b : A} (f : a ⟶ b) :
      θ.x f ≫ (e a).hom ▷ T.map f = S.map f ◁ (e b).hom ≫ ψ.x f := by
    rw [eq_of_heq (hx f), eq_of_heq (hy f)]
    exact hn f
  exact {
    hom := ⟨fun a => (e a).hom, fun f => nat f⟩
    inv := ⟨fun a => (e a).inv, fun {a b} f => by
      rw [← cancel_epi (whiskerLeftIso (R := k) (S.map f) (e b)).hom]
      simp only [whiskerLeftIso_hom]
      rw [← Category.assoc, ← nat f, Category.assoc, hom_inv_whiskerRight k,
        Category.comp_id, ← Category.assoc, whiskerLeft_hom_inv k, Category.id_comp]⟩
    hom_inv_id := TwoNatTrans.hom_ext fun a => (e a).hom_inv_id
    inv_hom_id := TwoNatTrans.hom_ext fun a => (e a).inv_hom_id }

def chevalleyQForwardCounitInvLeg : TwoNatTrans (F) ((F).comp ((G).comp (F))) :=
  qTriangleTransport (TwoSuperfunctor.comp_id (F)) rfl (TwoNatTrans.precompose (F) (K))

theorem chevalleyQForwardCounitInvLeg_X (a : A) :
    (chevalleyQForwardCounitInvLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).X a =
      (K).X ((F).obj a) := eq_of_heq (qTriangleTransport_X_heq _ _ _ a)

theorem chevalleyQForwardCounitInvLeg_x_heq {a b : A} (f : a ⟶ b) :
    HEq ((chevalleyQForwardCounitInvLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).x f)
      ((K).x ((F).map f)) :=
  qTriangleTransport_x_heq (TwoSuperfunctor.comp_id (F)) rfl
    (TwoNatTrans.precompose (F) (K)) f

/-- The unit after F is the inverse of the counit before F,
up to the identity comparison of F, not by changing either transformation. -/
def chevalleyQForwardUnitComparisonIso :
    chevalleyQForwardUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc) ≅
      chevalleyQForwardCounitInvLeg :=
  qTriangleIsoOfComponents _ _ (fun a => (F).map ((J).X a)) (fun a => (K).X ((F).obj a))
    (fun f => TwoNatTrans.postcomposeCell (F) (J) f)
    (fun f => (K).x ((F).map f))
    (funext chevalleyQForwardUnitLeg_X) (funext chevalleyQForwardCounitInvLeg_X)
    (fun f => chevalleyQForwardUnitLeg_x_heq f)
    (fun f => chevalleyQForwardCounitInvLeg_x_heq f)
    (fun a => qForwardUnitComparison (chevQ_negWeight_square a.as).symm)
    (fun f => by
      have h := qForwardUnitComparison_naturality _ _ f ((G).map ((F).map f))
        (qUnitHomCounit f) (chevalleyQReverseHomCounit ((F).map f)) (qUnitHomCounit_image f)
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => ((F).mapComp f ((J).X _)).hom ≫ z)
          (Category.assoc _ _ _)).trans h))
end OddMath.SKM
