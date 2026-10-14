/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQPiForwardLift

/-!
# Comparison of the legs of the first zigzag of `ω̃`

An even isomorphism from the unit leg `ω̃ ∘ J̃` to the leg `L̃ ∘ ω̃`, where `L̃` is the inverse counit of `ω̃`.

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
local notation "L" => chevalleyQGlobalCounitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "P" => PiSOp.twoFunctor (R := k) (B := A)
local notation "Q" => PiSOp.inverseTwoFunctor (R := k) (B := A)
local notation "Fπ" => chevalleyQPiTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Gπ" => chevalleyQPiReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Lπ" => chevalleyQPiGlobalCounitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "U" => chevalleyQForwardUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "V" => chevalleyQForwardCounitInvLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)

/-- counit reverse, precomposed by Fπ and transported by comp_id. -/
def chevalleyQPiForwardCounitInvLeg : TwoNatTrans (Fπ) ((Fπ).comp ((Gπ).comp (Fπ))) :=
  TwoNatTrans.rebase (TwoSuperfunctor.comp_id (Fπ)) rfl
    (TwoNatTrans.precompose (Fπ) (Lπ))

theorem qPiForward_bridge_cancel : (Fπ).comp (Q) = TwoEnvelope.mapPi (F) := by
  rw [← qPiForward_source, TwoSuperfunctor.comp_assoc,
    PiSOp.twoFunctor_comp_inverseTwoFunctor, TwoSuperfunctor.comp_id]

theorem qPiForward_rebase_heq
    {S S' T T' : TwoSuperfunctor k (TwoSOp k (QPiTwoEnvelope k (UGr D Sc sy hc)))
      (TwoSOp k (QPiTwoEnvelope k (UGr D Sc sy hc)))}
    (p : S = S') (q : T = T') (θ : TwoNatTrans S T) :
    HEq (qPiRebase p q θ) θ := by
  cases p
  cases q
  rfl

theorem qPiForward_inv_conjugate_heq :
    HEq (chevalleyQPiForwardCounitInvLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      (TwoNatTrans.postcompose (P)
        (TwoNatTrans.precompose (TwoEnvelope.mapPi (F)) (TwoEnvelope.mapPiNatTrans (L)))) := by
  have h₁ := TwoNatTrans.rebase_heq (TwoSuperfunctor.comp_id (Fπ)) rfl
    (TwoNatTrans.precompose (Fπ) (Lπ))
  have h₂ := TwoNatTrans.precompose_heq (Fπ)
    (qPiCounit_target (D := D) (Sc := Sc) (sy := sy) (hc := hc))
    (qPiCounit_source (D := D) (Sc := Sc) (sy := sy) (hc := hc))
    (qPiForward_rebase_heq (qPiCounit_target (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      (qPiCounit_source (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      (qPiCounitInvConjugate (D := D) (Sc := Sc) (sy := sy) (hc := hc))).symm
  have h₃ := TwoNatTrans.precompose_postcompose_heq (Fπ) (P) (TwoNatTrans.precompose (Q) (TwoEnvelope.mapPiNatTrans (L)))
  have h₄ := TwoNatTrans.postcompose_heq
    (TwoSuperfunctor.comp_assoc (Fπ) (Q)
      (TwoEnvelope.mapPi (TwoSuperfunctor.id k (TwoSOp k (A))))).symm
    (TwoSuperfunctor.comp_assoc (Fπ) (Q) (TwoEnvelope.mapPi ((G).comp (F)))).symm
    (P) (TwoNatTrans.precompose_precompose_heq (Fπ) (Q) (TwoEnvelope.mapPiNatTrans (L)))
  rw [qPiForward_bridge_cancel] at h₄
  exact h₁.trans (h₂.symm.trans (h₃.trans h₄))

theorem qPiForward_inv_heq :
    HEq (chevalleyQPiForwardCounitInvLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      (TwoNatTrans.postcompose (P) (TwoEnvelope.mapPiNatTrans (V))) := by
  have h₅ := TwoNatTrans.postcompose_heq
    (TwoEnvelope.mapPi_comp (F) (TwoSuperfunctor.id k (TwoSOp k (A))))
    (TwoEnvelope.mapPi_comp (F) ((G).comp (F))) (P) (TwoEnvelope.mapPiNatTrans_precompose_heq (F) (L))
  have h₆ := TwoEnvelope.mapPiNatTrans_heq (TwoSuperfunctor.comp_id (F)) rfl
    (TwoNatTrans.rebase_heq (TwoSuperfunctor.comp_id (F)) rfl (TwoNatTrans.precompose (F) (L))).symm
  have h₇ := TwoNatTrans.postcompose_heq (congrArg TwoEnvelope.mapPi (TwoSuperfunctor.comp_id (F))) rfl (P) h₆
  exact (qPiForward_inv_conjugate_heq (D := D) (Sc := Sc) (sy := sy) (hc := hc)).trans
    (h₅.symm.trans h₇)

/-- Compatibility for the two legs, retaining both grading proofs. -/
def qPiForwardLegComparison :
    EvenIso (chevalleyQPiForwardUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      chevalleyQPiForwardCounitInvLeg :=
  EvenIso.ofHEq qPiForward_source qPiForward_target qPiForward_unit_heq.symm qPiForward_inv_heq.symm
    (qPiForwardConjugatedComparison (D := D) (Sc := Sc) (sy := sy) (hc := hc))

def chevalleyQPiForwardUnitComparisonIso :
    chevalleyQPiForwardUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc) ≅
      chevalleyQPiForwardCounitInvLeg :=
  (qPiForwardLegComparison (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1

theorem chevalleyQPiForwardUnitComparisonIso_eq :
    chevalleyQPiForwardUnitComparisonIso (D := D) (Sc := Sc) (sy := sy) (hc := hc) =
      (qPiForwardLegComparison (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1 := rfl

theorem chevalleyQPiForwardUnitComparisonIso_homogeneous :
    (chevalleyQPiForwardUnitComparisonIso (D := D) (Sc := Sc)
      (sy := sy) (hc := hc)).hom.IsHomogeneous
      0 0 := by
  apply Eq.mpr (congrArg
    (fun z : chevalleyQPiForwardUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc) ≅
      chevalleyQPiForwardCounitInvLeg => z.hom.IsHomogeneous 0 0)
    (chevalleyQPiForwardUnitComparisonIso_eq (D := D) (Sc := Sc) (sy := sy) (hc := hc)))
  exact (qPiForwardLegComparison (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.1

theorem chevalleyQPiForwardUnitComparisonIso_inv_homogeneous :
    (chevalleyQPiForwardUnitComparisonIso (D := D) (Sc := Sc)
      (sy := sy) (hc := hc)).inv.IsHomogeneous
      0 0 := by
  apply Eq.mpr (congrArg
    (fun z : chevalleyQPiForwardUnitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc) ≅
      chevalleyQPiForwardCounitInvLeg => z.inv.IsHomogeneous 0 0)
    (chevalleyQPiForwardUnitComparisonIso_eq (D := D) (Sc := Sc) (sy := sy) (hc := hc)))
  exact (qPiForwardLegComparison (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.2
end OddMath.SKM
