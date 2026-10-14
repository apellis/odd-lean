/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQPiUnit
import OddMath.SKM.ChevalleyQUnitCancel

/-!
# The inverse unit of `ω̃`

`chevalleyQPiGlobalUnitInv : ω̃ ⋙ G̃ ⟹ 1`, the Π-envelope of the inverse unit of `ω_q`.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}
local notation "A" => QTwoEnvelope k (UGr D Sc sy hc)
local notation "Aπ" => QPiTwoEnvelope k (UGr D Sc sy hc)
local notation "Fπ" => chevalleyQPiTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Gπ" => chevalleyQPiReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "K" => chevalleyQGlobalUnitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)

/-- Reverse endpoint transport of the lifted Q reverse. -/
def chevalleyQPiGlobalUnitInv : TwoNatTrans ((Fπ).comp (Gπ)) (TwoSuperfunctor.id k (Aπ)) :=
  TwoNatTrans.rebase (qPiUnit_target (D := D) (Sc := Sc) (sy := sy) (hc := hc))
    (TwoEnvelope.mapPi_id k (A)) (TwoEnvelope.mapPiNatTrans (K))

local notation "Kπ" => chevalleyQPiGlobalUnitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)

theorem chevalleyQPiGlobalUnitInv_isStrong : (Kπ).IsStrong := by
  apply TwoNatTrans.rebase_isStrong
  exact TwoEnvelope.mapPiNatTrans_isStrong chevalleyQGlobalUnitInv_isStrong

theorem chevalleyQPiGlobalUnitInv_isGraded : (Kπ).IsGraded := by
  apply TwoNatTrans.rebase_isGraded
  exact TwoEnvelope.mapPiNatTrans_isGraded chevalleyQGlobalUnitInv_isGraded
end OddMath.SKM
