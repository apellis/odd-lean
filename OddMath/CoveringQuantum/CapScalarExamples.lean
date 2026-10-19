/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.CapScalar
import OddMath.CoveringQuantum.UDot.ContextualCommutatorExamples

/-! # Odd rank-one cap-scalar consumers

The existing odd root datum is tested at positive, zero and negative coroot
weights. The Laurent variable remains formal in the sign-minus countercheck.
-/
noncomputable section
namespace OddMath.CoveringQuantum.CapScalarExamples
open Coefficients CapScalar UDot
open OddMath.SKM.PositiveDecoratedFamilyCoefficientsExamples
open scoped LaurentSeries

private theorem odd_qi : oddDatum.qi Coefficients.q () = Coefficients.q := by
  simp [SuperCartanDatum.qi, oddDatum]

private theorem odd_pii : oddDatum.pii pi () = pi := by
  simp [SuperCartanDatum.pii, oddDatum, ZMod.val_one]

/-- At coroot weight two the direct expression is q⁻¹ + πq. -/
theorem odd_two : direct oddDatum () 2 =
    ((Coefficients.q⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring) +
      pi * (Coefficients.q : Coefficients.Ring) := by
  rw [direct_eq_bar, odd_qi, odd_pii]
  change bar (qpNat Coefficients.q pi 2) = _
  rw [qpNat_two, map_add, map_mul, bar_pi, bar_q]
  have h := bar_bar (Coefficients.q : Coefficients.Ring)
  rw [bar_q] at h
  rw [h]

/-- The printed unbarred quantum integer is not this direct contribution. -/
theorem odd_two_ne_unbarred : direct oddDatum () 2 ≠ qpInt Coefficients.q pi 2 := by
  rw [direct_eq_bar, odd_qi, odd_pii]
  exact UDot.ContextualCommutatorExamples.odd_two_bar_ne

/-- Arbitrary integral weights include zero. -/
theorem odd_zero : direct oddDatum () 0 = 0 := by
  rw [direct_eq_bar, odd_qi, odd_pii]
  change bar (qpInt Coefficients.q pi 0) = 0
  simp

/-- A negative-weight consumer uses inverse unit powers, not truncated powers. -/
theorem odd_negative_two : direct oddDatum () (-2) =
    -(((Coefficients.q⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring) +
      pi * (Coefficients.q : Coefficients.Ring)) := by
  rw [← odd_two, direct_eq_bar, direct_eq_bar, odd_qi, odd_pii]
  change bar (qpInt Coefficients.q pi (-2)) = -bar (qpInt Coefficients.q pi 2)
  rw [qpInt_neg pi_sq]
  norm_num [pi_sq]

/-- Odd coroot weights are also allowed by this datum. -/
theorem odd_one : direct oddDatum () 1 = 1 := by
  rw [direct_eq_bar, odd_qi, odd_pii]
  change bar (qpNat Coefficients.q pi 1) = 1
  simp

/-- Both parity specializations have the expected Laurent polynomial. -/
theorem odd_two_laurent (σ : ℚ) (hσ : σ ^ 2 = 1) :
    signLaurent σ hσ (direct oddDatum () 2) =
      (HahnSeries.single (-1) 1 + HahnSeries.single 1 σ : LaurentSeries ℚ) := by
  have hq : signLaurent σ hσ
      (((Coefficients.q⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring)) =
        HahnSeries.single (-1) 1 := by
    simpa only [qp, zpow_neg_one] using signLaurent_qp σ hσ (-1)
  rw [odd_two, map_add, map_mul, hq, signLaurent_pi, signLaurent_q]
  change _ + HahnSeries.single 0 σ * HahnSeries.single 1 1 = _
  rw [HahnSeries.single_mul_single, zero_add, mul_one]

/-- At π = -1 the q coefficient is -1 and the q⁻¹ coefficient is 1. -/
theorem odd_two_minus_coeff :
    (signLaurent (-1) (by norm_num) (direct oddDatum () 2)).coeff 1 = -1 ∧
    (signLaurent (-1) (by norm_num) (direct oddDatum () 2)).coeff (-1) = 1 := by
  rw [odd_two_laurent]
  norm_num [HahnSeries.coeff_add, HahnSeries.coeff_single]

/-- A nonconstant coefficient-algebra consumer shifts the correction by q³. -/
theorem odd_two_shifted_coeff :
    (signLaurent (-1) (by norm_num)
      (direct oddDatum () 2 * qp Coefficients.q 3)).coeff 4 = -1 := by
  rw [map_mul, odd_two_laurent, signLaurent_qp, add_mul,
    HahnSeries.single_mul_single, HahnSeries.single_mul_single]
  norm_num [HahnSeries.coeff_add, HahnSeries.coeff_single]

end OddMath.CoveringQuantum.CapScalarExamples
