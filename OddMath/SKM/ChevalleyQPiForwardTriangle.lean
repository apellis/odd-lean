/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQPiForwardComparison

/-!
# The first triangle identity of `ω̃`

`chevalleyQPiForwardTriangleIso`: the first zigzag of `ω̃` is isomorphic to the identity of `ω̃`, through an even isomorphism of degree zero.

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
local notation "Eπ" => chevalleyQPiGlobalCounit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Lπ" => chevalleyQPiGlobalCounitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)

def qPiForwardPairCancel :
    EvenIso ((chevalleyQPiForwardCounitInvLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)).vcomp
      chevalleyQPiForwardCounitLeg) (TwoNatTrans.id (Fπ)) :=
  EvenIso.zigzagCancel (Eπ) (Lπ) qPiCounitInvCancel

def qPiForwardTriangle :
    EvenIso (chevalleyQPiForwardZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      (TwoNatTrans.id (Fπ)) :=
  EvenIso.trans (EvenIso.whiskerRight qPiForwardLegComparison chevalleyQPiForwardCounitLeg) qPiForwardPairCancel

/-- The forward zigzag, with the functors, unit and counit. -/
def chevalleyQPiForwardTriangleIso :
    chevalleyQPiForwardZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc) ≅ TwoNatTrans.id (Fπ) :=
  (qPiForwardTriangle (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1

theorem chevalleyQPiForwardTriangleIso_eq :
    chevalleyQPiForwardTriangleIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) =
      (qPiForwardTriangle (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1 := rfl

theorem chevalleyQPiForwardTriangleIso_homogeneous :
    (chevalleyQPiForwardTriangleIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).hom.IsHomogeneous
      0 0 := by
  apply Eq.mpr (congrArg
    (fun z : chevalleyQPiForwardZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc) ≅
      TwoNatTrans.id (Fπ) => z.hom.IsHomogeneous 0 0)
    (chevalleyQPiForwardTriangleIso_eq (D := D) (Sc := Sc) (sy := sy) (hc := hc)))
  exact (qPiForwardTriangle (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.1

theorem chevalleyQPiForwardTriangleIso_inv_homogeneous :
    (chevalleyQPiForwardTriangleIso (D := D) (Sc := Sc) (sy := sy) (hc := hc)).inv.IsHomogeneous
      0 0 := by
  apply Eq.mpr (congrArg
    (fun z : chevalleyQPiForwardZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc) ≅
      TwoNatTrans.id (Fπ) => z.inv.IsHomogeneous 0 0)
    (chevalleyQPiForwardTriangleIso_eq (D := D) (Sc := Sc) (sy := sy) (hc := hc)))
  exact (qPiForwardTriangle (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.2
end OddMath.SKM
