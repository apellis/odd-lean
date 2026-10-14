/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQPiCounit
import OddMath.SKM.ChevalleyQCounitCancel

/-!
# The inverse counit of `ω̃`

`chevalleyQPiGlobalCounitInv : 1 ⟹ G̃ ⋙ ω̃`, obtained from the inverse counit of `ω_q` by the same conjugation.

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
local notation "T" => TwoSOp k (QPiTwoEnvelope k (UGr D Sc sy hc))
local notation "P" => PiSOp.twoFunctor (R := k) (B := A)
local notation "P⁻" => PiSOp.inverseTwoFunctor (R := k) (B := A)
local notation "L" => chevalleyQGlobalCounitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Fπ" => chevalleyQPiTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Gπ" => chevalleyQPiReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)

/-- The Q reverse, lifted and conjugated by the parity bridge. -/
def qPiCounitInvConjugate :=
  TwoNatTrans.postcompose (P) (TwoNatTrans.precompose (P⁻) (TwoEnvelope.mapPiNatTrans (L)))

/-- Endpoint transport is precisely the reverse of the counit's endpoint transport. -/
def chevalleyQPiGlobalCounitInv :
    TwoNatTrans (TwoSuperfunctor.id k (T)) (TwoSuperfunctor.comp (Gπ) (Fπ)) :=
  qPiRebase (qPiCounit_target (D := D) (Sc := Sc) (sy := sy) (hc := hc))
    (qPiCounit_source (D := D) (Sc := Sc) (sy := sy) (hc := hc))
    (qPiCounitInvConjugate (D := D) (Sc := Sc) (sy := sy) (hc := hc))

local notation "Lπ" => chevalleyQPiGlobalCounitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)

theorem chevalleyQPiGlobalCounitInv_isStrong : (Lπ).IsStrong := by
  apply qPiRebase_isStrong
  apply TwoNatTrans.postcompose_isStrong (P)
  apply TwoNatTrans.precompose_isStrong (P⁻)
  exact TwoEnvelope.mapPiNatTrans_isStrong chevalleyQGlobalCounitInv_isStrong

theorem chevalleyQPiGlobalCounitInv_isGraded : (Lπ).IsGraded := by
  apply qPiRebase_isGraded
  apply TwoNatTrans.postcompose_isGraded (P) PiSOp.twoFunctor_isGraded
  apply TwoNatTrans.precompose_isGraded (P⁻)
  exact TwoEnvelope.mapPiNatTrans_isGraded chevalleyQGlobalCounitInv_isGraded
end OddMath.SKM
