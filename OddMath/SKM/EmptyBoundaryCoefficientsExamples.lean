/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.EmptyBoundaryCoefficients
import OddMath.CoveringQuantum.UDot.ContextualExchangeExamples

/-! # Empty-boundary coefficient consumers

Complete internally chosen families on two odd colours. The nested cap word
has a same-colour interchange with nonempty context and a nonempty shorter word.
-/
noncomputable section
namespace OddMath.SKM.EmptyBoundaryCoefficientsExamples
open StringDiagrams StringDiagrams.Chord
open CoveringQuantum CoveringQuantum.Coefficients CoveringQuantum.UDot.GenericTensor
open CoveringQuantum.UDot.GenericVerma.MixedGram
open CoveringQuantum.UDot.ContextualExchangeExamples

/-- A nested pair of caps requiring the same-colour interchange. -/
def nestedWord : List (Letter Bool) :=
  [(true, true), (true, false), (false, false), (false, true)]

/-- A complete family with choices made before weight, sign or degree. -/
def family (a : List (Letter Bool)) : CoefficientFamily a :=
  (exists_complete_coefficientFamily a).choose

theorem family_complete (a : List (Letter Bool)) : (family a).Complete :=
  (exists_complete_coefficientFamily a).choose_spec

private theorem nested_matching :
    IsMatching₂ nestedWord [] [.cap 1, .cap 0] := by
  refine ⟨⟨?_, ?_⟩, rfl⟩
  · exact ⟨(4, (true, false)), (2, (false, false)), rfl, rfl, rfl, by decide⟩
  · exact ⟨⟨(6, (true, true)), (0, (false, true)), rfl, rfl, rfl,
      by change (6 : ℕ) ≠ 0; decide⟩, trivial⟩

/-- The chosen complete family for the nested word is genuinely inhabited. -/
theorem nested_family_nonempty : (family nestedWord).members.Nonempty := by
  obtain ⟨R, hR, hr, _⟩ := exists_strictReduced_equiv nested_matching
  obtain ⟨S, hS, _⟩ := family_complete nestedWord R hR hr
  exact ⟨S, hS⟩

/-- Same-colour interchange, shorter comparison, and all choice hypotheses are
fully discharged for an arbitrary weight and every Laurent coefficient. -/
theorem nested_coeff (μ : Bool → ℤ) (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (signLaurent σ hσ (sesquilinearForm twoOddDatum twoOdd_barConsistent
      (algebraWord twoOddDatum μ nestedWord) (algebraWord twoOddDatum μ []))).coeff z =
      (family nestedWord).coeff twoOddDatum.toSKM twoOddDatum.skmSymmetrizer μ σ z :=
  empty_boundary_labelled_form_coeff nestedWord (family nestedWord)
    (family_complete nestedWord) twoOddDatum twoOdd_barConsistent μ σ hσ z

/-- Distinct-colour interchange in nonempty context, with no supplied IH. -/
theorem distinct_coeff (μ : Bool → ℤ) (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    let a : List (Letter Bool) :=
      [(false, false), (true, false), (false, true), (true, true)]
    (signLaurent σ hσ (sesquilinearForm twoOddDatum twoOdd_barConsistent
      (algebraWord twoOddDatum μ a) (algebraWord twoOddDatum μ []))).coeff z =
      (family a).coeff twoOddDatum.toSKM twoOddDatum.skmSymmetrizer μ σ z :=
  empty_boundary_labelled_form_coeff _ (family _) (family_complete _)
    twoOddDatum twoOdd_barConsistent μ σ hσ z

/-- Both square-one rational signs are concrete importing consumers. -/
theorem nested_both_signs (μ : Bool → ℤ) (z : ℤ) :
    (signLaurent 1 (by norm_num) (sesquilinearForm twoOddDatum twoOdd_barConsistent
      (algebraWord twoOddDatum μ nestedWord) (algebraWord twoOddDatum μ []))).coeff z =
      (family nestedWord).coeff twoOddDatum.toSKM twoOddDatum.skmSymmetrizer μ 1 z ∧
    (signLaurent (-1) (by norm_num) (sesquilinearForm twoOddDatum twoOdd_barConsistent
      (algebraWord twoOddDatum μ nestedWord) (algebraWord twoOddDatum μ []))).coeff z =
      (family nestedWord).coeff twoOddDatum.toSKM twoOddDatum.skmSymmetrizer μ (-1) z :=
  ⟨nested_coeff μ 1 (by norm_num) z, nested_coeff μ (-1) (by norm_num) z⟩

end OddMath.SKM.EmptyBoundaryCoefficientsExamples
