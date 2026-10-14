/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQPiForwardZigzag
import OddMath.SKM.ChevalleyQForwardTriangleGrading

/-!
# The unit leg of the first zigzag of `ω̃`

The leg `ω̃ ∘ J̃` is heterogeneously equal to the parity-bridge conjugate of the Π-envelope of `ω_q ∘ J`. The comparison of `ω_q ∘ J` with `L ∘ ω_q` (`L` the inverse counit) extends to the Π-envelope.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory BicategoryStruct

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}
local notation "A" => QTwoEnvelope k (UGr D Sc sy hc)
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "G" => chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "J" => chevalleyQGlobalUnit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "L" => chevalleyQGlobalCounitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "P" => PiSOp.twoFunctor (R := k) (B := A)
local notation "Q" => PiSOp.inverseTwoFunctor (R := k) (B := A)
local notation "Fπ" => chevalleyQPiTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Gπ" => chevalleyQPiReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Jπ" => chevalleyQPiGlobalUnit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Lπ" => chevalleyQPiGlobalCounitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "U" => chevalleyQForwardUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "V" => chevalleyQForwardCounitInvLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)

def qPiForwardBaseComparison : EvenIso (U) (V) :=
  ⟨chevalleyQForwardUnitComparisonIso, chevalleyQForwardUnitComparisonIso_homogeneous,
    TwoNatTrans.inv_isHomogeneous_of_hom _ chevalleyQForwardUnitComparisonIso_homogeneous⟩

def qPiForwardLiftedComparison := EvenIso.mapPi
  (qPiForwardBaseComparison (D := D) (Sc := Sc) (sy := sy) (hc := hc))

def qPiForwardConjugatedComparison :
    EvenIso (TwoNatTrans.postcompose (P) (TwoEnvelope.mapPiNatTrans (U)))
      (TwoNatTrans.postcompose (P) (TwoEnvelope.mapPiNatTrans (V))) :=
  ⟨(TwoNatTrans.postcomposition (P) _ _).mapIso
      (qPiForwardLiftedComparison (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1,
    TwoNatTrans.postcomposeModification_isHomogeneous (P) PiSOp.twoFunctor_isGraded
      (qPiForwardLiftedComparison (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.1,
    TwoNatTrans.postcomposeModification_isHomogeneous (P) PiSOp.twoFunctor_isGraded
      (qPiForwardLiftedComparison (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.2⟩

theorem qPiForward_source : (TwoEnvelope.mapPi (F)).comp (P) = (Fπ) := by
  simp only [chevalleyQPiTwo]

theorem qPiForward_target :
    (TwoEnvelope.mapPi ((F).comp ((G).comp (F)))).comp (P) =
      (Fπ).comp ((Gπ).comp (Fπ)) := by
  rw [TwoEnvelope.mapPi_comp, TwoEnvelope.mapPi_comp,
    ← TwoSuperfunctor.comp_assoc, qPiUnit_composite,
    TwoSuperfunctor.comp_assoc, qPiForward_source, TwoSuperfunctor.comp_assoc]

/-- The unit leg, extended to Π-envelopes and conjugated by the parity bridge. -/
theorem qPiForward_unit_heq :
    HEq (chevalleyQPiForwardUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      (TwoNatTrans.postcompose (P) (TwoEnvelope.mapPiNatTrans (U))) := by
  have h₁ := TwoNatTrans.rebase_heq (TwoSuperfunctor.id_comp (Fπ))
    (TwoSuperfunctor.comp_assoc (Fπ) (Gπ) (Fπ)) (TwoNatTrans.postcompose (Fπ) (Jπ))
  have h₂ := TwoNatTrans.postcompose_heq (TwoEnvelope.mapPi_id k (A))
    (qPiUnit_target (D := D) (Sc := Sc) (sy := sy) (hc := hc)) (Fπ)
    (TwoNatTrans.rebase_heq (TwoEnvelope.mapPi_id k (A))
      (qPiUnit_target (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      (TwoEnvelope.mapPiNatTrans (J))).symm
  have h₃ := TwoNatTrans.postcompose_comp_heq (TwoEnvelope.mapPi (F)) (P) (TwoEnvelope.mapPiNatTrans (J))
  rw [qPiForward_source] at h₃
  have h₄ := TwoNatTrans.postcompose_heq (TwoEnvelope.mapPi_comp (TwoSuperfunctor.id k (A)) (F))
    (TwoEnvelope.mapPi_comp ((F).comp (G)) (F)) (P) (TwoEnvelope.mapPiNatTrans_postcompose_heq (F) (J))
  have h₅ := TwoEnvelope.mapPiNatTrans_heq (TwoSuperfunctor.id_comp (F))
    (TwoSuperfunctor.comp_assoc (F) (G) (F))
    (TwoNatTrans.rebase_heq (TwoSuperfunctor.id_comp (F))
      (TwoSuperfunctor.comp_assoc (F) (G) (F)) (TwoNatTrans.postcompose (F) (J))).symm
  have h₆ := TwoNatTrans.postcompose_heq (congrArg TwoEnvelope.mapPi (TwoSuperfunctor.id_comp (F)))
    (congrArg TwoEnvelope.mapPi (TwoSuperfunctor.comp_assoc (F) (G) (F))) (P) h₅
  exact h₁.trans (h₂.symm.trans (h₃.trans (h₄.symm.trans h₆)))
end OddMath.SKM
