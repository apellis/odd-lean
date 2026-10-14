/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQPiForwardTriangle
import OddMath.SKM.ChevalleyQReverseTriangleGrading

/-!
# The second zigzag of `ω̃`

`chevalleyQPiReverseZigzag : G̃ ⟹ G̃`, the right zigzag `RightZigzag.zigzag` of the unit and counit of `ω̃`, with its components.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section

namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}
local notation "Fπ" => chevalleyQPiTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Gπ" => chevalleyQPiReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Jπ" => chevalleyQPiGlobalUnit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Eπ" => chevalleyQPiGlobalCounit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Kπ" => chevalleyQPiGlobalUnitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)

def chevalleyQPiReverseUnitLeg : TwoNatTrans (Gπ) ((Gπ).comp ((Fπ).comp (Gπ))) :=
  RightZigzag.unitLeg (Fπ) (Gπ) (Jπ)

def chevalleyQPiReverseCounitLeg : TwoNatTrans ((Gπ).comp ((Fπ).comp (Gπ))) (Gπ) :=
  RightZigzag.counitLeg (Fπ) (Gπ) (Eπ)

def chevalleyQPiReverseUnitInvLeg : TwoNatTrans ((Gπ).comp ((Fπ).comp (Gπ))) (Gπ) :=
  TwoNatTrans.rebase rfl (TwoSuperfunctor.comp_id (Gπ)) (TwoNatTrans.precompose (Gπ) (Kπ))

def chevalleyQPiReverseZigzag : TwoNatTrans (Gπ) (Gπ) :=
  chevalleyQPiReverseUnitLeg.vcomp chevalleyQPiReverseCounitLeg

theorem chevalleyQPiReverseZigzag_eq :
    chevalleyQPiReverseZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc) =
      RightZigzag.zigzag (Fπ) (Gπ) (Jπ) (Eπ) := rfl

theorem chevalleyQPiReverseZigzag_X (b : TwoSOp k (QPiTwoEnvelope k (UGr D Sc sy hc))) :
    (chevalleyQPiReverseZigzag (D := D) (Sc := Sc) (sy := sy) (hc := hc)).X b =
      (Jπ).X ((Gπ).obj b) ≫ (Gπ).map ((Eπ).X b) := by
  rw [chevalleyQPiReverseZigzag_eq]
  exact RightZigzag.zigzag_X (Fπ) (Gπ) (Jπ) (Eπ) b
end OddMath.SKM
