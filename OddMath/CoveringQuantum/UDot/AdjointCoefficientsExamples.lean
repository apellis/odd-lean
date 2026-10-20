/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.PositiveAdjointCoefficients
import OddMath.SKM.PositiveFormCoefficientsExamples

/-! # Odd rank-one upward adjoint coefficient examples -/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.AdjointCoefficientsExamples
open OddMath.CoveringQuantum UDot UDot.GenericTensor
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.SKM.PositiveFormCoefficientsExamples
open Coefficients PreF

/-- Nonempty odd-root consumer of the physical left-cons theorem:
a = [i], b = [i,i], μ = 0, ν = 2, δ = 3 and F's right weight is 4.
The coefficient at 1 is σ, hence nonzero for both sign specializations. -/
theorem repeated_odd_physical_bent_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) :
    (signLaurent σ hσ (sesquilinearForm oddDatum
      (positiveHalf oddDatum Coefficients.q pi 0
        (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [()])))
      (⟨F oddDatum Coefficients.q pi () 4,
        F_mem_modified oddDatum Coefficients.q pi () 4⟩ *
        positiveHalf oddDatum Coefficients.q pi 0
          (oddDatum.toSerreF Coefficients.q pi
            (monomial Coefficients.Ring [(), ()]))))).coeff 1 = σ := by
  have h := sesquilinearForm_positive_leftCons_bent_coeff oddDatum
    σ hσ () 0 [()] [(), ()] 1
  have hw : OddMath.SKM.wt oddDatum.toSKM 0
      (([()] : List Unit).map fun i => (true, i)) = 2 := by
    rw [positive_word_physical_weight]
    simp [halfWeight, wordWeight, halfRoot, oddDatum]
  dsimp only at h
  rw [hw] at h
  have hh : (oddDatum.d () : ℤ) * (1 + oddDatum.h () 2) = 3 := by rfl
  rw [hh] at h
  have hc := (repeated_negative_coeff σ hσ).1
  change (signLaurent σ hσ (sesquilinearForm oddDatum
    (positiveHalf oddDatum Coefficients.q pi 0
      (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [(), ()])))
    (positiveHalf oddDatum Coefficients.q pi 0
      (oddDatum.toSerreF Coefficients.q pi
        (monomial Coefficients.Ring [(), ()]))))).coeff (-2) = σ at hc
  exact h.trans hc

/-- The two sign specializations both give nonzero coefficients. -/
theorem repeated_odd_physical_both_signs :
    (signLaurent 1 (by norm_num) (sesquilinearForm oddDatum
      (positiveHalf oddDatum Coefficients.q pi 0
        (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [()])))
      (⟨F oddDatum Coefficients.q pi () 4,
        F_mem_modified oddDatum Coefficients.q pi () 4⟩ *
        positiveHalf oddDatum Coefficients.q pi 0
          (oddDatum.toSerreF Coefficients.q pi
            (monomial Coefficients.Ring [(), ()]))))).coeff 1 = 1 ∧
    (signLaurent (-1) (by norm_num) (sesquilinearForm oddDatum
      (positiveHalf oddDatum Coefficients.q pi 0
        (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [()])))
      (⟨F oddDatum Coefficients.q pi () 4,
        F_mem_modified oddDatum Coefficients.q pi () 4⟩ *
        positiveHalf oddDatum Coefficients.q pi 0
          (oddDatum.toSerreF Coefficients.q pi
            (monomial Coefficients.Ring [(), ()]))))).coeff 1 = -1 := by
  exact ⟨repeated_odd_physical_bent_coeff 1 (by norm_num),
    repeated_odd_physical_bent_coeff (-1) (by norm_num)⟩

end OddMath.CoveringQuantum.UDot.AdjointCoefficientsExamples

namespace OddMath.CoveringQuantum.UDot.AdjointCoefficientsExamples
open OddMath.CoveringQuantum UDot UDot.GenericTensor
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.SKM.PositiveFormCoefficientsExamples
open Coefficients PreF

/-- A genuinely nonempty repeated odd-root test: δ = 3; the bent coefficient
at 1 is the old coefficient at -2, namely σ, not σ times an additional cup sign. -/
theorem repeated_odd_bent_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) :
    (signLaurent σ hσ (sesquilinearForm oddDatum
      (positiveHalf oddDatum Coefficients.q pi 0
        (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [()])))
      (⟨F oddDatum Coefficients.q pi () 4,
        F_mem_modified oddDatum Coefficients.q pi () 4⟩ *
        positiveHalf oddDatum Coefficients.q pi 0
          (oddDatum.toSerreF Coefficients.q pi
            (monomial Coefficients.Ring [(), ()]))))).coeff 1 = σ := by
  have h := sesquilinearForm_E_reversed_coeff oddDatum σ hσ
    () 0 [()]
    (positiveHalf oddDatum Coefficients.q pi 0
      (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [(), ()]))) 1
  have hw : (0 : ℤ) + halfWeight oddDatum true (wordWeight ([()] : List Unit).reverse) = 2 := by
    simp [halfWeight, wordWeight, halfRoot, oddDatum]
  dsimp only at h
  rw [hw] at h
  have hh : (oddDatum.d () : ℤ) * (1 + oddDatum.h () 2) = 3 := by rfl
  rw [hh] at h
  have hc := (repeated_negative_coeff σ hσ).1
  change (signLaurent σ hσ (sesquilinearForm oddDatum
    (positiveHalf oddDatum Coefficients.q pi 0
      (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [(), ()])))
    (positiveHalf oddDatum Coefficients.q pi 0
      (oddDatum.toSerreF Coefficients.q pi
        (monomial Coefficients.Ring [(), ()]))))).coeff (-2) = σ at hc
  exact h.trans hc

end OddMath.CoveringQuantum.UDot.AdjointCoefficientsExamples
