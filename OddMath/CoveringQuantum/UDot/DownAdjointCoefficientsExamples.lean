/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.MixedAdjointCoefficients
import OddMath.CoveringQuantum.UDot.PositiveAdjointCoefficients
import OddMath.SKM.PositiveFormCoefficientsExamples
import OddMath.CoveringQuantum.UDot.TensorGram.MixedIntegration

/-! Nonzero odd-root consumers for the downward adjoint, including its parity factor. -/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.DownAdjointExamples
open OddMath.CoveringQuantum UDot UDot.GenericTensor
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.SKM.PositiveFormCoefficientsExamples
open Coefficients PreF

/-- The actual downward mixed form, not an assumed pairing value. -/
def downPairing : Coefficients.Ring :=
  sesquilinearForm oddDatum
    (⟨F oddDatum Coefficients.q pi () 4,
      F_mem_modified oddDatum Coefficients.q pi () 4⟩ *
      positiveHalf oddDatum Coefficients.q pi 0
        (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [(), ()])))
    (positiveHalf oddDatum Coefficients.q pi 0
      (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [()])))

/-- ν=4, adjoint E weight2, δ=−3 and parity1. The known coefficient at−2
of the repeated positive pair is σ; the new theorem retains the extra σ. -/
theorem repeated_odd_down_sign_relation (σ : ℚ) (hσ : σ ^ 2 = 1) :
    σ = σ * (signLaurent σ hσ downPairing).coeff 1 := by
  have h := sesquilinearForm_F_bent_coeff oddDatum σ hσ () 4
    (positiveHalf oddDatum Coefficients.q pi 0
      (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [(), ()])))
    (positiveHalf oddDatum Coefficients.q pi 0
      (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [()]))) (-2)
  have he := positiveHalf_leftCons oddDatum () 0 [()]
  have hw : (0 : ℤ) + halfWeight oddDatum true (wordWeight ([()] : List Unit)) = 2 := by
    simp [halfWeight, wordWeight, halfRoot, oddDatum]
  rw [hw] at he
  have hp : (oddDatum.parl () 4).val = 1 := by decide
  have hd : (oddDatum.d () : ℤ) * (1 - oddDatum.h () 4) = -3 := rfl
  rw [hp, pow_one, hd] at h
  change (signLaurent σ hσ (sesquilinearForm oddDatum _
    (⟨E oddDatum Coefficients.q pi () 2,
      E_mem_modified oddDatum Coefficients.q pi () 2⟩ * _))).coeff (-2) =
      σ * (signLaurent σ hσ downPairing).coeff 1 at h
  rw [he] at h
  have hc := (repeated_negative_coeff σ hσ).1
  change (signLaurent σ hσ (sesquilinearForm oddDatum
    (positiveHalf oddDatum Coefficients.q pi 0
      (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [(), ()])))
    (positiveHalf oddDatum Coefficients.q pi 0
      (oddDatum.toSerreF Coefficients.q pi
        (monomial Coefficients.Ring [(), ()]))))).coeff (-2) = σ at hc
  exact hc.symm.trans h

/-- Cancellation uses σ²=1; the nonzero result exercises the new downward shift. -/
theorem repeated_odd_down_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) :
    (signLaurent σ hσ downPairing).coeff 1 = 1 := by
  have hs : σ ≠ 0 := by intro hz; simp [hz] at hσ
  apply mul_left_cancel₀ hs
  simpa only [mul_one] using (repeated_odd_down_sign_relation σ hσ).symm

/-- Both specializations are nonzero, with the odd prefactor present in the derivation. -/
theorem repeated_odd_down_both_signs :
    (signLaurent 1 (by norm_num) downPairing).coeff 1 = 1 ∧
    (signLaurent (-1) (by norm_num) downPairing).coeff 1 = 1 :=
  ⟨repeated_odd_down_coeff 1 (by norm_num), repeated_odd_down_coeff (-1) (by norm_num)⟩

/-- The physical mixed-word theorem itself gives the nonzero downward coefficient. -/
theorem repeated_odd_physical_down_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) :
    (signLaurent σ hσ (sesquilinearForm oddDatum
      (GenericVerma.MixedGram.algebraWord oddDatum 0
        [(false, ()), (true, ()), (true, ())])
      (GenericVerma.MixedGram.algebraWord oddDatum 0 [(true, ())]))).coeff 1 = 1 := by
  have h := sesquilinearForm_mixed_down_leftCons_bent_coeff oddDatum
    σ hσ () 0 [(true, ()), (true, ())] [(true, ())] (by rfl) (-2)
  dsimp only at h
  have hν : OddMath.SKM.wt oddDatum.toSKM 0 [(true, ()), (true, ())] = 4 := rfl
  rw [hν] at h
  have hp : (oddDatum.parl () 4).val = 1 := by decide
  have hd : (oddDatum.d () : ℤ) * (1 - oddDatum.h () 4) = -3 := rfl
  rw [hp, pow_one, hd] at h
  norm_num only at h
  have hpos (u : List Unit) :
      GenericVerma.MixedGram.algebraWord oddDatum 0 (TensorPositive.pos u) =
        positiveHalf oddDatum Coefficients.q pi 0
          (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring u)) := by
    rw [PositiveComparison.algebraWord_pos_eq]
    apply Subtype.ext
    exact (halfMap_monomial oddDatum Coefficients.q pi true u 0).symm
  have hh : GenericVerma.MixedGram.algebraWord oddDatum 0 [(true, ()), (true, ())] =
      positiveHalf oddDatum Coefficients.q pi 0
        (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [(), ()])) :=
    hpos [(), ()]
  simp only [hh] at h
  have hc := (repeated_negative_coeff σ hσ).1
  change (signLaurent σ hσ (sesquilinearForm oddDatum
    (positiveHalf oddDatum Coefficients.q pi 0
      (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [(), ()])))
    (positiveHalf oddDatum Coefficients.q pi 0
      (oddDatum.toSerreF Coefficients.q pi
        (monomial Coefficients.Ring [(), ()]))))).coeff (-2) = σ at hc
  rw [hc] at h
  have hs : σ ≠ 0 := by intro hz; simp [hz] at hσ
  apply mul_left_cancel₀ hs
  simpa only [mul_one] using h.symm

end OddMath.CoveringQuantum.UDot.DownAdjointExamples
