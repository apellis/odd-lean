/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.DownAdjointCoefficients
import OddMath.CoveringQuantum.UDot.PositiveAdjointCoefficients
import OddMath.CoveringQuantum.UDot.SesquilinearFormExamples

/-!
# Word coefficients with infinite colours and a negative right weight

The positive-word coefficient formula and the E/F adjoint steps of BE2,
arXiv:1701.04133v2, Theorem 10.3 apply to the constructed sesquilinear form on
`VermaWeightExamples.datum`. The colour type is `ℕ`, and bar consistency fails.
The words contain repeated and distinct colours. The common right weight has
negative colour-zero pairing. No nonzero value or graphical identity is asserted.
The Laurent expansion retains source-to-target permutations, integer guards and
the geometric dot factors; its inputs are the specified reversed positive words.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.CoveringQuantum.UDot.WordCoefficientExamples
open Coefficients PreF GenericTensor VermaWeightExamples TriangularRepresentationExamples

/-- The underlying datum has infinitely many colours and is not bar-consistent. -/
theorem infinite_nonbar : Infinite ℕ ∧ ¬ datum.toSuperCartanDatum.BarConsistent :=
  ⟨infinite_colours, not_barConsistent⟩

/-- The common right weight is negative at colour zero. -/
theorem negative_right_weight : datum.h 0 baseWeight = -3 :=
  SesquilinearFormExamples.negative_weight

/-- A nonempty source word with repeated zero and distinct one. -/
def sourceColours : Fin 3 → ℕ := ![0, 0, 1]

/-- A target word with the same colours in a different order. -/
def targetColours : Fin 3 → ℕ := ![0, 1, 0]

/-- The actual source word, before reversal in the positive input. -/
theorem source_word : List.ofFn sourceColours = [0, 0, 1] := by decide

/-- The actual target word, before reversal in the positive input. -/
theorem target_word : List.ofFn targetColours = [0, 1, 0] := by decide

/-- Reversed positive source input in the actual modified algebra. -/
def sourceInput : modified datum Coefficients.q pi :=
  positiveHalf datum Coefficients.q pi baseWeight
    (datum.toSerreF Coefficients.q pi
      (monomial Coefficients.Ring (List.ofFn sourceColours).reverse))

/-- Reversed positive target input in the actual modified algebra. -/
def targetInput : modified datum Coefficients.q pi :=
  positiveHalf datum Coefficients.q pi baseWeight
    (datum.toSerreF Coefficients.q pi
      (monomial Coefficients.Ring (List.ofFn targetColours).reverse))

/-- The constructed form has the unchanged weighted-permutation normalization. -/
theorem word_normalization :
    sesquilinearForm datum sourceInput targetInput =
      (∏ r, datum.norm Coefficients.q pi (sourceColours r)) *
        ∑ w : Equiv.Perm (Fin 3), if ∀ r, sourceColours r = targetColours (w r) then
          ∏ r, ∏ s with r < s ∧ w s < w r,
            datum.chi Coefficients.q pi (sourceColours r) (sourceColours s)
        else 0 :=
  sesquilinearForm_positive_words_permutations datum baseWeight 3 sourceColours targetColours

/-- Both sign specializations of the actual form obey the guarded Laurent formula. -/
theorem word_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    let C := datum.toSuperCartanDatum
    let κ : Equiv.Perm (Fin 3) → ℤ := fun w =>
      ∑ r, ∑ s with r < s ∧ w s < w r, -C.dot (sourceColours r) (sourceColours s)
    let ε : Equiv.Perm (Fin 3) → ZMod 2 := fun w =>
      ∑ r, ∑ s with r < s ∧ w s < w r,
        datum.parity (sourceColours r) * datum.parity (sourceColours s)
    (signLaurent σ hσ (sesquilinearForm datum sourceInput targetInput)).coeff z =
      ∑ w : Equiv.Perm (Fin 3), if ∀ r, sourceColours r = targetColours (w r) then
        if κ w ≤ z then σ ^ (ε w).val *
          PowerSeries.coeff (z - κ w).toNat (C.dotSeries σ targetColours)
        else 0
      else 0 :=
  sesquilinearForm_positive_words_coeff datum σ hσ baseWeight 3 sourceColours targetColours z

/-- The E step uses the actual endpoint of the reversed source word. -/
theorem E_word_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    let ν := baseWeight + halfWeight datum true (wordWeight (List.ofFn sourceColours).reverse)
    (signLaurent σ hσ (sesquilinearForm datum sourceInput
      (⟨F datum Coefficients.q pi 0 (ν + datum.α 0),
        F_mem_modified datum Coefficients.q pi 0 (ν + datum.α 0)⟩ * targetInput))).coeff z =
    (signLaurent σ hσ (sesquilinearForm datum
      (positiveHalf datum Coefficients.q pi baseWeight
        (datum.toSerreF Coefficients.q pi
          (monomial Coefficients.Ring ((List.ofFn sourceColours) ++ [0]).reverse)))
      targetInput)).coeff (z - datum.d 0 * (1 + datum.h 0 ν)) :=
  sesquilinearForm_E_reversed_coeff datum σ hσ 0 baseWeight
    (List.ofFn sourceColours) targetInput z

/-- The downward step retains the original star parity factor and integral shift. -/
theorem F_word_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    let ν := baseWeight + halfWeight datum true (wordWeight (List.ofFn sourceColours).reverse)
    (signLaurent σ hσ (sesquilinearForm datum sourceInput
      (⟨E datum Coefficients.q pi 0 (ν - datum.α 0),
        E_mem_modified datum Coefficients.q pi 0 (ν - datum.α 0)⟩ * targetInput))).coeff z =
    σ ^ (datum.parl 0 ν).val *
      (signLaurent σ hσ (sesquilinearForm datum
        (⟨F datum Coefficients.q pi 0 ν, F_mem_modified datum Coefficients.q pi 0 ν⟩ *
          sourceInput) targetInput)).coeff (z - datum.d 0 * (1 - datum.h 0 ν)) :=
  sesquilinearForm_F_bent_coeff datum σ hσ 0 _ sourceInput targetInput z

/-- The first slot still conjugates q before any sign specialization. -/
theorem word_first_slot :
    sesquilinearForm datum ((Coefficients.q : Coefficients.Ring) • sourceInput) targetInput =
      bar (Coefficients.q : Coefficients.Ring) *
        sesquilinearForm datum sourceInput targetInput := by
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]

end OddMath.CoveringQuantum.UDot.WordCoefficientExamples
