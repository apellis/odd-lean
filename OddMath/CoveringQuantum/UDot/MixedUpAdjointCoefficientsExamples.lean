/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.MixedUpAdjointCoefficients
import OddMath.CoveringQuantum.UDot.AdjointCoefficientsExamples
import OddMath.CoveringQuantum.UDot.TensorGram.MixedIntegration

/-! A mixed-sign consumer of the physical upward coefficient bridge. -/
noncomputable section
namespace OddMath.CoveringQuantum.UDot.MixedUpAdjointExamples
open OddMath.CoveringQuantum UDot UDot.GenericTensor
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open OddMath.SKM.PositiveFormCoefficientsExamples
open Coefficients PreF GenericVerma.MixedGram

/-- The empty word paired with the signed word F F E E in right column zero. -/
def mixedCupPairing : Coefficients.Ring :=
  sesquilinearForm oddDatum
    (algebraWord oddDatum 0 [])
    (algebraWord oddDatum 0 [(false, ()), (false, ()), (true, ()), (true, ())])

/-- The new headline is applied with a=[] and b=[down,up,up], not an all-positive
pair. Here ν=0, F's right weight is 2, and δ=1. The old mixed coefficient at 1
is σ by the existing evaluated odd-root form, hence the new coefficient at 2 is σ. -/
theorem odd_mixed_up_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) :
    (signLaurent σ hσ mixedCupPairing).coeff 2 = σ := by
  have h := sesquilinearForm_mixed_up_leftCons_bent_coeff oddDatum
    σ hσ () 0 [] [(false, ()), (true, ()), (true, ())] (by rfl) 2
  dsimp only at h
  have hd : (oddDatum.d () : ℤ) *
      (1 + oddDatum.h () (OddMath.SKM.wt oddDatum.toSKM 0 [])) = 1 := rfl
  rw [hd] at h
  norm_num only at h
  have hpos (u : List Unit) :
      algebraWord oddDatum 0 (TensorPositive.pos u) =
        positiveHalf oddDatum Coefficients.q pi 0
          (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring u)) := by
    rw [PositiveComparison.algebraWord_pos_eq]
    apply Subtype.ext
    exact (halfMap_monomial oddDatum Coefficients.q pi true u 0).symm
  have hu : algebraWord oddDatum 0 [(true, ())] =
      positiveHalf oddDatum Coefficients.q pi 0
        (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [()])) :=
    hpos [()]
  have huu : algebraWord oddDatum 0 [(true, ()), (true, ())] =
      positiveHalf oddDatum Coefficients.q pi 0
        (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [(), ()])) :=
    hpos [(), ()]
  have hm : algebraWord oddDatum 0 [(false, ()), (true, ()), (true, ())] =
      (⟨F oddDatum Coefficients.q pi () 4,
        F_mem_modified oddDatum Coefficients.q pi () 4⟩ : modified oddDatum Coefficients.q pi) *
        positiveHalf oddDatum Coefficients.q pi 0
          (oddDatum.toSerreF Coefficients.q pi (monomial Coefficients.Ring [(), ()])) := by
    change (⟨F oddDatum Coefficients.q pi () 4, _⟩ : modified oddDatum Coefficients.q pi) *
      algebraWord oddDatum 0 [(true, ()), (true, ())] = _
    rw [huu]
  rw [hu, hm] at h
  exact h.trans (AdjointCoefficientsExamples.repeated_odd_physical_bent_coeff σ hσ)

/-- Both sign specializations give explicitly nonzero coefficients of a mixed word. -/
theorem odd_mixed_up_both_signs :
    (signLaurent 1 (by norm_num) mixedCupPairing).coeff 2 = 1 ∧
    (signLaurent (-1) (by norm_num) mixedCupPairing).coeff 2 = -1 ∧
    (signLaurent 1 (by norm_num) mixedCupPairing).coeff 2 ≠ 0 ∧
    (signLaurent (-1) (by norm_num) mixedCupPairing).coeff 2 ≠ 0 := by
  have hp := odd_mixed_up_coeff 1 (by norm_num)
  have hn := odd_mixed_up_coeff (-1) (by norm_num)
  simp only [hp, hn]
  norm_num

end OddMath.CoveringQuantum.UDot.MixedUpAdjointExamples
