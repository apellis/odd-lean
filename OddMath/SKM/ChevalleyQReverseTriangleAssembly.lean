/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQReverseZigzag
import OddMath.SKM.ChevalleyQReverseTriangleNaturality

/-!
# Assembly of the second triangle of `ω_q`

An isomorphism of transformations from componentwise data, applied to the second zigzag.

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
local notation "K" => chevalleyQGlobalUnitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)

theorem qReversePostcompose_x_heq (P : TwoSuperfunctor k B A) (Q : TwoSuperfunctor k A B)
    (θ : TwoNatTrans (P.comp Q) (TwoSuperfunctor.id k B)) {a b : B} (f : a ⟶ b) :
    HEq ((qReverseTransport (TwoSuperfunctor.comp_assoc P Q P) (TwoSuperfunctor.id_comp P)
      (TwoNatTrans.postcompose P θ)).x f) (TwoNatTrans.postcomposeCell P θ f) :=
  qReverseTransport_x_heq _ _ _ f

def qReverseIsoOfComponents {S T : TwoSuperfunctor k B A} (θ ψ : TwoNatTrans S T)
    (U V : ∀ a, S.obj a ⟶ T.obj a)
    (x : ∀ {a b : B} (f : a ⟶ b), S.map f ≫ U b ⟶ U a ≫ T.map f)
    (y : ∀ {a b : B} (f : a ⟶ b), S.map f ≫ V b ⟶ V a ≫ T.map f)
    (hU : θ.X = U) (hV : ψ.X = V)
    (hx : ∀ {a b : B} (f : a ⟶ b), HEq (θ.x f) (x f))
    (hy : ∀ {a b : B} (f : a ⟶ b), HEq (ψ.x f) (y f))
    (e : ∀ a, U a ≅ V a)
    (hn : ∀ {a b : B} (f : a ⟶ b),
      x f ≫ (e a).hom ▷ T.map f = S.map f ◁ (e b).hom ≫ y f) : θ ≅ ψ := by
  subst U V
  have nat {a b : B} (f : a ⟶ b) :
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

def chevalleyQReverseUnitInvLeg : TwoNatTrans ((G).comp ((F).comp (G))) (G) :=
  qReverseTransport rfl (TwoSuperfunctor.comp_id (G)) (TwoNatTrans.precompose (G) (K))

theorem chevalleyQReverseUnitInvLeg_X (b : B) :
    (chevalleyQReverseUnitInvLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).X b =
      (K).X ((G).obj b) := eq_of_heq (qReverseTransport_X_heq _ _ _ b)

theorem chevalleyQReverseUnitInvLeg_x_heq {a b : B} (f : a ⟶ b) :
    HEq ((chevalleyQReverseUnitInvLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).x f)
      ((K).x ((G).map f)) :=
  qReverseTransport_x_heq rfl (TwoSuperfunctor.comp_id (G))
    (TwoNatTrans.precompose (G) (K)) f

def qReverseCompareIso (P : TwoSuperfunctor k B A) (Q : TwoSuperfunctor k A B)
    (θ : TwoNatTrans (P.comp Q) (TwoSuperfunctor.id k B))
    (ψ : TwoNatTrans (Q.comp P) (TwoSuperfunctor.id k A))
    (e : ∀ b, P.map (θ.X b) ≅ ψ.X (P.obj b))
    (hn : ∀ {a b : B} (f : a ⟶ b),
      TwoNatTrans.postcomposeCell P θ f ≫ (e a).hom ▷ P.map f =
        P.map (Q.map (P.map f)) ◁ (e b).hom ≫ ψ.x (P.map f)) :
    qReverseTransport (TwoSuperfunctor.comp_assoc P Q P) (TwoSuperfunctor.id_comp P)
      (TwoNatTrans.postcompose P θ) ≅
    qReverseTransport rfl (TwoSuperfunctor.comp_id P) (TwoNatTrans.precompose P ψ) :=
  qReverseIsoOfComponents _ _ (fun b => P.map (θ.X b)) (fun b => ψ.X (P.obj b))
    (fun f => TwoNatTrans.postcomposeCell P θ f) (fun f => ψ.x (P.map f))
    (funext fun b => eq_of_heq (qReverseTransport_X_heq _ _ _ b))
    (funext fun b => eq_of_heq (qReverseTransport_X_heq _ _ _ b))
    (fun f => qReversePostcompose_x_heq P Q θ f)
    (fun f => qReverseTransport_x_heq _ _ _ f) e hn

theorem qReverseComparison_naturality {a b : B} (f : a ⟶ b) :
    TwoNatTrans.postcomposeCell (G) (E) f ≫
      (qReverseCounitComparison (chevQ_negWeight_square a.unop.as).symm).hom ▷ (G).map f =
    (G).map ((F).map ((G).map f)) ◁
      (qReverseCounitComparison (chevQ_negWeight_square b.unop.as).symm).hom ≫
      (K).x ((G).map f) := by
  have h := qReverseCounitComparison_naturality _ _ f ((F).map ((G).map f))
    (chevalleyQReverseHomCounit f) (qUnitHomCounit ((G).map f))
    (qReverseHomCounit_comparison f)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => ((G).mapComp ((F).map ((G).map f)) ((E).X _)).hom ≫ z)
      (Category.assoc _ _ _)).trans h)

/-- The exact counit after G compares to the exact inverse unit before G. -/
def chevalleyQReverseCounitComparisonIso :
    chevalleyQReverseCounitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc) ≅
      chevalleyQReverseUnitInvLeg :=
  qReverseCompareIso (G) (F) (E) (K)
    (fun b => qReverseCounitComparison (chevQ_negWeight_square b.unop.as).symm)
    (fun f => qReverseComparison_naturality f)

end OddMath.SKM
