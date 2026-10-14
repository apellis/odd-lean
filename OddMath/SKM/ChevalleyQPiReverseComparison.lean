/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyQPiReverseZigzag

/-!
# Comparison of the legs of the second zigzag of `ω̃`

An even isomorphism from the counit leg `G̃ ∘ Ẽ` to the leg `K̃ ∘ G̃`, where `K̃` is the inverse unit of `ω̃`. It extends the corresponding comparison for `ω_q` to the Π-envelope.

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
local notation "E" => chevalleyQGlobalCounit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "K" => chevalleyQGlobalUnitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "P" => PiSOp.twoFunctor (R := k) (B := A)
local notation "Q" => PiSOp.inverseTwoFunctor (R := k) (B := A)
local notation "Fπ" => chevalleyQPiTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Gπ" => chevalleyQPiReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Eπ" => chevalleyQPiGlobalCounit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "Kπ" => chevalleyQPiGlobalUnitInv (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "U" => chevalleyQReverseCounitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "V" => chevalleyQReverseUnitInvLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc)

def qPiReverseBaseComparison : EvenIso (U) (V) :=
  ⟨chevalleyQReverseCounitComparisonIso, chevalleyQReverseCounitComparisonIso_homogeneous,
    TwoNatTrans.inv_isHomogeneous_of_hom _ chevalleyQReverseCounitComparisonIso_homogeneous⟩

def qPiReverseLiftedComparison := EvenIso.mapPi
  (qPiReverseBaseComparison (D := D) (Sc := Sc) (sy := sy) (hc := hc))

def qPiReverseConjugatedComparison :
    EvenIso (TwoNatTrans.precompose (Q) (TwoEnvelope.mapPiNatTrans (U)))
      (TwoNatTrans.precompose (Q) (TwoEnvelope.mapPiNatTrans (V))) :=
  ⟨(TwoNatTrans.precomposition (Q) _ _).mapIso
      (qPiReverseLiftedComparison (D := D) (Sc := Sc) (sy := sy) (hc := hc)).1,
    TwoNatTrans.precomposeModification_isHomogeneous (Q)
      (qPiReverseLiftedComparison (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.1,
    TwoNatTrans.precomposeModification_isHomogeneous (Q)
      (qPiReverseLiftedComparison (D := D) (Sc := Sc) (sy := sy) (hc := hc)).2.2⟩

theorem qPiReverse_target : (Q).comp (TwoEnvelope.mapPi (G)) = (Gπ) := by
  simp only [chevalleyQPiReverseTwo]

theorem qPiReverse_source :
    (Q).comp (TwoEnvelope.mapPi ((G).comp ((F).comp (G)))) =
      (Gπ).comp ((Fπ).comp (Gπ)) := by
  rw [TwoEnvelope.mapPi_comp, TwoEnvelope.mapPi_comp, qPiUnit_composite,
    ← TwoSuperfunctor.comp_assoc, qPiReverse_target]

theorem qPiReverse_bridge_cancel : (P).comp (Gπ) = TwoEnvelope.mapPi (G) := by
  rw [← qPiReverse_target, ← TwoSuperfunctor.comp_assoc,
    PiSOp.twoFunctor_comp_inverseTwoFunctor, TwoSuperfunctor.id_comp]

theorem qPiReverse_q_rebase_heq
    {S S' T T' : TwoSuperfunctor k (TwoSOp k (A)) (A)}
    (p : S = S') (q : T = T') (θ : TwoNatTrans S T) :
    HEq (qReverseTransport p q θ) θ := by
  cases p
  cases q
  rfl

theorem qPiReverse_counit_conjugate_heq :
    HEq (chevalleyQPiReverseCounitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      (TwoNatTrans.precompose (Q)
        (TwoNatTrans.postcompose (TwoEnvelope.mapPi (G)) (TwoEnvelope.mapPiNatTrans (E)))) := by
  have h₁ := TwoNatTrans.rebase_heq (TwoSuperfunctor.comp_assoc (Gπ) (Fπ) (Gπ))
    (TwoSuperfunctor.id_comp (Gπ)) (TwoNatTrans.postcompose (Gπ) (Eπ))
  have h₂ := TwoNatTrans.postcompose_heq
    (qPiCounit_source (D := D) (Sc := Sc) (sy := sy) (hc := hc))
    (qPiCounit_target (D := D) (Sc := Sc) (sy := sy) (hc := hc)) (Gπ)
    (qPiForward_rebase_heq (qPiCounit_source (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      (qPiCounit_target (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      (qPiCounitConjugate (D := D) (Sc := Sc) (sy := sy) (hc := hc))).symm
  have h₃ := TwoNatTrans.postcompose_comp_heq (P) (Gπ) (TwoNatTrans.precompose (Q) (TwoEnvelope.mapPiNatTrans (E)))
  rw [qPiReverse_bridge_cancel] at h₃
  have h₄ := TwoNatTrans.precompose_postcompose_heq (Q) (TwoEnvelope.mapPi (G)) (TwoEnvelope.mapPiNatTrans (E))
  exact h₁.trans (h₂.symm.trans (h₃.symm.trans h₄.symm))

theorem qPiReverse_counit_heq :
    HEq (chevalleyQPiReverseCounitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      (TwoNatTrans.precompose (Q) (TwoEnvelope.mapPiNatTrans (U))) := by
  have h₅ := TwoNatTrans.precompose_heq (Q)
    (TwoEnvelope.mapPi_comp ((G).comp (F)) (G))
    (TwoEnvelope.mapPi_comp (TwoSuperfunctor.id k (TwoSOp k (A))) (G)) (TwoEnvelope.mapPiNatTrans_postcompose_heq (G) (E))
  have h₆ := TwoEnvelope.mapPiNatTrans_heq (TwoSuperfunctor.comp_assoc (G) (F) (G))
    (TwoSuperfunctor.id_comp (G))
    (qPiReverse_q_rebase_heq (TwoSuperfunctor.comp_assoc (G) (F) (G))
      (TwoSuperfunctor.id_comp (G)) (TwoNatTrans.postcompose (G) (E))).symm
  have h₇ := TwoNatTrans.precompose_heq (Q)
    (congrArg TwoEnvelope.mapPi (TwoSuperfunctor.comp_assoc (G) (F) (G)))
    (congrArg TwoEnvelope.mapPi (TwoSuperfunctor.id_comp (G))) h₆
  exact (qPiReverse_counit_conjugate_heq (D := D) (Sc := Sc) (sy := sy) (hc := hc)).trans
    (h₅.symm.trans h₇)

theorem qPiReverse_inv_heq :
    HEq (chevalleyQPiReverseUnitInvLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      (TwoNatTrans.precompose (Q) (TwoEnvelope.mapPiNatTrans (V))) := by
  have h₁ := TwoNatTrans.rebase_heq rfl (TwoSuperfunctor.comp_id (Gπ)) (TwoNatTrans.precompose (Gπ) (Kπ))
  have h₂ := TwoNatTrans.precompose_heq (Gπ) (qPiUnit_target (D := D) (Sc := Sc) (sy := sy) (hc := hc))
    (TwoEnvelope.mapPi_id k (A))
    (TwoNatTrans.rebase_heq (qPiUnit_target (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      (TwoEnvelope.mapPi_id k (A)) (TwoEnvelope.mapPiNatTrans (K))).symm
  have h₃ := TwoNatTrans.precompose_precompose_heq (Q) (TwoEnvelope.mapPi (G)) (TwoEnvelope.mapPiNatTrans (K))
  rw [qPiReverse_target] at h₃
  have h₄ := TwoNatTrans.precompose_heq (Q) (TwoEnvelope.mapPi_comp (G) ((F).comp (G)))
    (TwoEnvelope.mapPi_comp (G) (TwoSuperfunctor.id k (A))) (TwoEnvelope.mapPiNatTrans_precompose_heq (G) (K))
  have h₅ := TwoEnvelope.mapPiNatTrans_heq rfl (TwoSuperfunctor.comp_id (G))
    (qPiReverse_q_rebase_heq rfl (TwoSuperfunctor.comp_id (G))
      (TwoNatTrans.precompose (G) (K))).symm
  have h₆ := TwoNatTrans.precompose_heq (Q) rfl (congrArg TwoEnvelope.mapPi (TwoSuperfunctor.comp_id (G))) h₅
  exact h₁.trans (h₂.symm.trans (h₃.symm.trans (h₄.symm.trans h₆)))

/-- Compatibility of the postcomposed counit with the precomposed unit inverse. -/
def qPiReverseLegComparison :
    EvenIso (chevalleyQPiReverseCounitLeg (D := D) (Sc := Sc) (sy := sy) (hc := hc))
      chevalleyQPiReverseUnitInvLeg :=
  EvenIso.ofHEq qPiReverse_source qPiReverse_target qPiReverse_counit_heq.symm qPiReverse_inv_heq.symm
    (qPiReverseConjugatedComparison (D := D) (Sc := Sc) (sy := sy) (hc := hc))
end OddMath.SKM
