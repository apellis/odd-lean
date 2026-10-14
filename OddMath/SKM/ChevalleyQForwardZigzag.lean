/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQForwardTriangleComponent
import StringDiagrams.Super.TwoFunctorPostcomposition
import StringDiagrams.Super.TwoSCat

/-!
# The first zigzag of `ω_q`

`chevalleyQForwardZigzag : ω_q ⟹ ω_q`, the composite of `ω_q ∘ J` and `E ∘ ω_q`, with legs transported along the associativity and unit equalities of composition.

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

/-- Boundary transport for the A/B pair. The pinned generic-looking
transportBoundary API is specialized to QPi envelopes and cannot apply here. -/
def qTriangleTransport {S T S' T' : TwoSuperfunctor k A B}
    (p : S = S') (q : T = T') (θ : TwoNatTrans S T) : TwoNatTrans S' T' := by
  cases p
  cases q
  exact θ

theorem qTriangleTransport_X_heq {S T S' T' : TwoSuperfunctor k A B}
    (p : S = S') (q : T = T') (θ : TwoNatTrans S T) (a : A) :
    HEq ((qTriangleTransport p q θ).X a) (θ.X a) := by
  cases p
  cases q
  rfl

theorem qTriangleTransport_x_heq {S T S' T' : TwoSuperfunctor k A B}
    (p : S = S') (q : T = T') (θ : TwoNatTrans S T) {a b : A} (f : a ⟶ b) :
    HEq ((qTriangleTransport p q θ).x f) (θ.x f) := by
  cases p
  cases q
  rfl

def chevalleyQForwardUnitLeg : TwoNatTrans (F) ((F).comp ((G).comp (F))) :=
  qTriangleTransport (TwoSuperfunctor.id_comp (F)) (TwoSuperfunctor.comp_assoc (F) (G) (F))
    (TwoNatTrans.postcompose (F) (J))

def chevalleyQForwardCounitLeg : TwoNatTrans ((F).comp ((G).comp (F))) (F) :=
  qTriangleTransport rfl (TwoSuperfunctor.comp_id (F)) (TwoNatTrans.precompose (F) (E))

/-- The postcomposed unit followed by the precomposed
counit, retyped along equality of functor records. -/
def chevalleyQForwardZigzag : TwoNatTrans (F) (F) :=
  chevalleyQForwardUnitLeg.vcomp chevalleyQForwardCounitLeg

theorem chevalleyQForwardUnitLeg_X (a : A) :
    (chevalleyQForwardUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).X a =
      (F).map ((J).X a) :=
  eq_of_heq (qTriangleTransport_X_heq _ _ _ a)

theorem chevalleyQForwardCounitLeg_X (a : A) :
    (chevalleyQForwardCounitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).X a =
      (E).X ((F).obj a) :=
  eq_of_heq (qTriangleTransport_X_heq _ _ _ a)

theorem chevalleyQForwardZigzag_X (a : A) :
    (chevalleyQForwardZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc)).X a =
      (F).map ((J).X a) ≫ (E).X ((F).obj a) := by
  change chevalleyQForwardUnitLeg.X a ≫ chevalleyQForwardCounitLeg.X a = _
  rw [chevalleyQForwardUnitLeg_X, chevalleyQForwardCounitLeg_X]
theorem chevalleyQForwardUnitLeg_x_heq {a b : A} (f : a ⟶ b) :
    HEq ((chevalleyQForwardUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).x f)
      (TwoNatTrans.postcomposeCell (F) (J) f) :=
  qTriangleTransport_x_heq (TwoSuperfunctor.id_comp (F))
    (TwoSuperfunctor.comp_assoc (F) (G) (F)) (TwoNatTrans.postcompose (F) (J)) f

theorem chevalleyQForwardCounitLeg_x_heq {a b : A} (f : a ⟶ b) :
    HEq ((chevalleyQForwardCounitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).x f)
      ((E).x ((F).map f)) :=
  qTriangleTransport_x_heq rfl (TwoSuperfunctor.comp_id (F))
    (TwoNatTrans.precompose (F) (E)) f

end OddMath.SKM
