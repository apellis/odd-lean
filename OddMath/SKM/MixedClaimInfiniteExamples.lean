/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.MatchingFamilyChoice
import OddMath.SKM.PositiveLabelledCoefficients
import OddMath.CoveringQuantum.UDot.MixedWordStepExamples

/-! # Graphical Claim 5 on infinitely many non-bar-consistent colours

Complete families and their serializers are constructed by matching existence.
The shorter empty-boundary comparison is discharged by the positive labelled
coefficient theorem. The same-colour interchange is the corrected Claim 5 of
BE2, arXiv:1701.04133v2, Theorem 10.3, with no new comparison premise.
-/

noncomputable section
namespace OddMath.SKM.MixedClaimInfiniteExamples
open StringDiagrams StringDiagrams.Chord
open CoveringQuantum CoveringQuantum.Coefficients CoveringQuantum.UDot
open GenericTensor GenericVerma.MixedGram VermaWeightExamples
open scoped BigOperators

/-- The colour set is infinite and the actual datum is not bar consistent. -/
theorem infinite_nonbar : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent :=
  ⟨infinite_colours, not_barConsistent⟩

/-- Families are chosen before any weight, sign or degree. -/
def family (a : List (Letter ℕ)) : CoefficientFamily a :=
  (exists_complete_coefficientFamily a).choose

/-- Completeness comes from the matching existence theorem. -/
theorem family_complete (a : List (Letter ℕ)) : (family a).Complete :=
  (exists_complete_coefficientFamily a).choose_spec

private theorem empty_comparison (μ : ℕ →₀ ℤ) (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (family []).coeff datum.toSKM datum.skmSymmetrizer μ σ z =
      (signLaurent σ hσ (sesquilinearForm datum
        (algebraWord datum μ []) (algebraWord datum μ []))).coeff z := by
  classical
  let K := family []
  obtain ⟨L, hL, hm, hc⟩ := positive_labelled_family_form_coeff datum μ
    (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)
    K.members K.matching (family_complete []) K.unique K.points K.onStrand
    K.serialize K.decorates
  obtain ⟨hf, he⟩ := hc σ hσ z
  have hd (t) := tableDegree_diagram datum.toSKM datum.skmSymmetrizer μ (L t) (hL t)
  simp only [hm] at hd
  have hw : algebraWord datum μ [] = positiveHalf datum Coefficients.q pi μ
      (datum.toSerreF Coefficients.q pi (PreF.monomial Coefficients.Ring [])) := by
    apply Subtype.ext
    simp only [PreF.monomial_nil, map_one, positiveHalf_one, algebraWord]
  have he' : (∑ t ∈ hf.toFinset,
      σ ^ (xpar datum.toSKM μ (dLay [] (K.serialize t.1 t.2))).val) =
      (signLaurent σ hσ (sesquilinearForm datum
        (algebraWord datum μ []) (algebraWord datum μ []))).coeff z := by
    simpa only [List.ofFn_zero, List.reverse_nil, ← hw] using he
  rw [← he']
  unfold CoefficientFamily.coeff
  apply Finset.sum_congr
  · ext t
    simp only [Set.Finite.mem_toFinset, CoefficientFamily.degree]
    exact ⟨fun h => (hd t).symm.trans h, fun h => (hd t).trans h⟩
  · intro t _
    rfl

/-- The actual shorter boundary equality, at a negative external weight. -/
theorem shorter_coefficients (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (family []).coeff datum.toSKM datum.skmSymmetrizer
      MixedWordStepExamples.rightWeight σ z =
      (signLaurent σ hσ (sesquilinearForm datum
        (algebraWord datum MixedWordStepExamples.rightWeight [])
        (algebraWord datum MixedWordStepExamples.rightWeight []))).coeff z :=
  empty_comparison _ σ hσ z

/-- Corrected same-colour graphical interchange, with complete families and the
shortened-word premise constructed, for every external weight and both signs. -/
theorem same_colour_iff (μ : ℕ →₀ ℤ) :
    ((∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
      (signLaurent σ hσ (sesquilinearForm datum
        (algebraWord datum μ [(true, 0), (false, 0)])
        (algebraWord datum μ []))).coeff z =
          (family [(true, 0), (false, 0)]).coeff
            datum.toSKM datum.skmSymmetrizer μ σ z) ↔
     (∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
      (signLaurent σ hσ (sesquilinearForm datum
        (algebraWord datum μ [(false, 0), (true, 0)])
        (algebraWord datum μ []))).coeff z =
          (family [(false, 0), (true, 0)]).coeff
            datum.toSKM datum.skmSymmetrizer μ σ z)) := by
  exact same_boundary_labelled_form_coeff_iff (a := []) (b := []) (i := 0)
    (family [(true, 0), (false, 0)]) (family [(false, 0), (true, 0)]) (family [])
    (family_complete _) (family_complete _) (family_complete _) datum μ
    (empty_comparison μ)

/-- The direct graphical scalar is the bar of the quantum integer at the
physical suffix weight, even with nonempty suffix and negative external weight. -/
theorem physical_suffix_scalar (σ : ℚ) (hσ : σ ^ 2 = 1) :
    claim5CapSeries datum.toSKM datum.skmSymmetrizer MixedWordStepExamples.rightWeight
      [(true, 0)] true 0 σ - HahnSeries.C (σ ^ (datum.parity 0).val) *
      claim5CapSeries datum.toSKM datum.skmSymmetrizer MixedWordStepExamples.rightWeight
        [(true, 0)] false 0 σ =
      signLaurent σ hσ (bar (qpInt (datum.qi Coefficients.q 0) (datum.pii pi 0) (-1))) := by
  simpa only [MixedWordStepExamples.suffix_pairing] using
    claim5_cap_scalar datum MixedWordStepExamples.rightWeight [(true, 0)] 0 σ hσ

end OddMath.SKM.MixedClaimInfiniteExamples
