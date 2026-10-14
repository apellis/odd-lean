/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQPiReverseComparison
import OddMath.SKM.ChevalleyQPiUnitCancel

/-!
# The second triangle identity of `ω̃`

`chevalleyQPiReverseTriangleIso`: the second zigzag of `ω̃` is isomorphic to the identity of `G̃`, through an even isomorphism of degree zero.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section

namespace OddMath.SKM
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}
local notation "Fπ" => chevalleyQPiTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Gπ" => chevalleyQPiReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Jπ" => chevalleyQPiGlobalUnit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Kπ" => chevalleyQPiGlobalUnitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)

def qPiReversePairCancel :
    EvenIso ((chevalleyQPiReverseUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).vcomp
      chevalleyQPiReverseUnitInvLeg) (TwoNatTrans.id (Gπ)) :=
  EvenIso.zigzagCancel (Kπ) (Jπ) qPiUnitCancel

def qPiReverseTriangle :
    EvenIso (chevalleyQPiReverseZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      (TwoNatTrans.id (Gπ)) :=
  EvenIso.trans (EvenIso.whiskerLeft chevalleyQPiReverseUnitLeg qPiReverseLegComparison) qPiReversePairCancel

/-- Isomorphism from the reverse zigzag, without replacing either leg. -/
def chevalleyQPiReverseTriangleIso :
    chevalleyQPiReverseZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc) ≅ TwoNatTrans.id (Gπ) :=
  (qPiReverseTriangle (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1

theorem chevalleyQPiReverseTriangleIso_eq :
    chevalleyQPiReverseTriangleIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) =
      (qPiReverseTriangle (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1 := rfl

theorem chevalleyQPiReverseTriangleIso_homogeneous :
    (chevalleyQPiReverseTriangleIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).hom.IsHomogeneous
      0 0 := by
  apply Eq.mpr (congrArg
    (fun z : chevalleyQPiReverseZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc) ≅
      TwoNatTrans.id (Gπ) => z.hom.IsHomogeneous 0 0)
    (chevalleyQPiReverseTriangleIso_eq (D := D) (Sc := Sc) (sy := sy) (hc := hc)))
  exact (qPiReverseTriangle (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.1

theorem chevalleyQPiReverseTriangleIso_inv_homogeneous :
    (chevalleyQPiReverseTriangleIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).inv.IsHomogeneous
      0 0 := by
  apply Eq.mpr (congrArg
    (fun z : chevalleyQPiReverseZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc) ≅
      TwoNatTrans.id (Gπ) => z.inv.IsHomogeneous 0 0)
    (chevalleyQPiReverseTriangleIso_eq (D := D) (Sc := Sc) (sy := sy) (hc := hc)))
  exact (qPiReverseTriangle (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.2
end OddMath.SKM
