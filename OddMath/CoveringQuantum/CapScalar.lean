/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.Coefficients
import OddMath.CoveringQuantum.UDot.AdjointCoefficients
import OddMath.SKM.CoveringDatum

/-! # The direct cap scalar

The scalar simplification in BE2, arXiv:1701.04133v2, Theorem 10.3 Claim 5,
with the outer bar removed from the cap expression and the quantum integer
barred. This is a scalar identity only, not the graphical Claim 5.
-/
noncomputable section
namespace OddMath.CoveringQuantum
namespace CapScalar
open UDot Coefficients

private theorem quantum_mul_sub {k : Type*} [CommRing k]
    (u : kˣ) (p : k) (hp : p ^ 2 = 1) (n : ℤ) :
    ((u : k) - p * ((u⁻¹ : kˣ) : k)) * qpInt u p n =
      qp u n - p ^ n.natAbs * qp u (-n) := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa only [qp, qpInt_ofNat, zpow_natCast, zpow_neg,
      ← inv_pow, Units.val_pow_eq_pow_val, Int.natAbs_natCast] using
      qpNat_mul_sub (q := u) (π := p) m
  · simpa only [qp, zpow_natCast, zpow_neg, neg_neg,
      ← inv_pow, Units.val_pow_eq_pow_val, Int.natAbs_neg, Int.natAbs_natCast] using
      qpInt_neg_mul_sub (q := u) hp m

/-- The denominator-multiplied identity over any commutative ring, at every
integer weight. In particular no field or domain hypothesis is used. -/
theorem denominator_mul_inverse_quantum {k : Type*} [CommRing k]
    (u : kˣ) (p : k) (hp : p ^ 2 = 1) (n : ℤ) :
    (1 - p * (u : k) ^ 2) * qpInt u⁻¹ p n =
      qp u (1 - n) - p ^ n.natAbs * qp u (1 + n) := by
  have h := quantum_mul_sub u⁻¹ p hp n
  simp only [inv_inv] at h
  have hn (a : ℤ) : qp u⁻¹ a = qp u (-a) := by
    simp only [qp, inv_zpow, zpow_neg]
  rw [hn, hn, neg_neg] at h
  have hmul (a : ℤ) : (u : k) * qp u a = qp u (1 + a) := by
    simpa only [qp, zpow_one] using (qp_mul (q := u) 1 a)
  calc
    _ = (u : k) * (((u⁻¹ : kˣ) : k) - p * (u : k)) * qpInt u⁻¹ p n := by
      rw [mul_sub, Units.mul_inv]; ring
    _ = (u : k) * (qp u (-n) - p ^ n.natAbs * qp u n) := by rw [mul_assoc, h]
    _ = _ := by rw [mul_sub, mul_left_comm (u : k), hmul, hmul]; rfl

variable {I X : Type*} [AddCommGroup X] (D : RootDatum I X)

/-- The parity in the cap expression is the existing root-datum parity;
its product with πᵢ is πᵢ to the coroot weight, read modulo two. -/
theorem cap_parity (i : I) (ν : X) :
    D.pii pi i * pi ^ (D.parl i ν).val = D.pii pi i ^ (D.h i ν).natAbs := by
  rw [UDot.pow_parl pi_sq, ← pow_succ']
  have hm : ((D.h i ν - 1).natAbs + 1) % 2 = (D.h i ν).natAbs % 2 := by
    rcases Int.natAbs_eq (D.h i ν - 1) with ha | ha <;>
      rcases Int.natAbs_eq (D.h i ν) with hb | hb <;> omega
  rw [← Nat.div_add_mod ((D.h i ν - 1).natAbs + 1) 2,
    ← Nat.div_add_mod (D.h i ν).natAbs 2]
  simp only [pow_add, pow_mul, D.pii_sq pi pi_sq, one_pow, one_mul, hm]

/-- Direct cap contribution, using the proved normalization inverse in the
covering coefficient ring, not division in an assumed field. -/
def direct (i : I) (ν : X) : Coefficients.Ring :=
  (qp (D.qi Coefficients.q i) (1 - D.h i ν) -
    D.pii pi i * pi ^ (D.parl i ν).val * qp (D.qi Coefficients.q i) (1 + D.h i ν)) *
    D.norm Coefficients.q pi i

/-- The corrected cap scalar is the barred quantum integer, for arbitrary
root datum and weight. Bar consistency and finiteness are not needed for
this scalar identity (they remain hypotheses of the constructed form). -/
theorem direct_eq_bar (i : I) (ν : X) :
    direct D i ν = bar (qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i ν)) := by
  rw [OddMath.CoveringQuantum.map_qpInt, barData.units_map_qi,
    barData.map_pii, direct, cap_parity]
  rw [← denominator_mul_inverse_quantum _ _ (D.pii_sq pi pi_sq i)]
  rw [mul_right_comm, denominator_mul_norm, one_mul]

/-- The cap parity agrees definitionally with the graphical datum, for all
weights, not just weights satisfying an inferred evenness condition. -/
theorem parl_eq_ipar (i : I) (ν : X) :
    D.parl i ν = OddMath.SKM.ipar D.toSKM i ν := rfl

open scoped LaurentSeries

/-- Laurent expansion of the normalization is the existing geometric dot factor. -/
theorem signLaurent_norm (σ : ℚ) (hσ : σ ^ 2 = 1) (i : I) :
    signLaurent σ hσ (D.norm Coefficients.q pi i) =
      (PreF.DotSeries.factor (D.pii σ i) (2 * D.d i)
        (Nat.ne_of_gt (by have := D.d_pos i; omega)) : LaurentSeries ℚ) := by
  let d : LaurentSeries ℚ :=
    1 - HahnSeries.C (D.pii σ i) * HahnSeries.single 1 1 ^ (2 * D.d i)
  have hn : d * signLaurent σ hσ (D.norm Coefficients.q pi i) = 1 := by
    have h := congrArg (signLaurent σ hσ) (denominator_mul_norm D.toSuperCartanDatum i)
    simpa only [d, SuperCartanDatum.pii, SuperCartanDatum.qi,
      Units.val_pow_eq_pow_val, map_mul, map_sub, map_pow, map_one,
      signLaurent_pi, signLaurent_q, ← pow_mul, Nat.mul_comm] using h
  have hf : (PreF.DotSeries.factor (D.pii σ i) (2 * D.d i)
      (Nat.ne_of_gt (by have := D.d_pos i; omega)) : LaurentSeries ℚ) * d = 1 := by
    have h := congrArg (HahnSeries.ofPowerSeries ℤ ℚ)
      (PreF.DotSeries.factor_mul (D.pii σ i) (2 * D.d i)
        (Nat.ne_of_gt (by have := D.d_pos i; omega)))
    simpa only [d, map_mul, map_sub, map_pow, map_one, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X] using h
  exact (left_inv_eq_right_inv hf hn).symm

private theorem signLaurent_qi (σ : ℚ) (hσ : σ ^ 2 = 1) (i : I) (z : ℤ) :
    signLaurent σ hσ (qp (D.qi Coefficients.q i) z) =
      (HahnSeries.single ((D.d i : ℤ) * z) 1 : LaurentSeries ℚ) := by
  rw [SuperCartanDatum.qi, qp, ← zpow_natCast, ← zpow_mul]
  exact signLaurent_qp σ hσ _

/-- The two direct cap shifts times the geometric dot series equal the Laurent
expansion of the barred quantum integer. Bar is applied in the covering ring
before expansion; it is not extended to arbitrary Laurent series. -/
theorem series_eq_bar (σ : ℚ) (hσ : σ ^ 2 = 1) (i : I) (ν : X) :
    (HahnSeries.single ((D.d i : ℤ) * (1 - D.h i ν)) 1 -
      HahnSeries.C (D.pii σ i * σ ^ (D.parl i ν).val) *
        HahnSeries.single ((D.d i : ℤ) * (1 + D.h i ν)) 1) *
      (PreF.DotSeries.factor (D.pii σ i) (2 * D.d i)
        (Nat.ne_of_gt (by have := D.d_pos i; omega)) : LaurentSeries ℚ) =
    signLaurent σ hσ (bar (qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i ν))) := by
  rw [← direct_eq_bar, direct]
  simp only [map_mul, map_sub, map_pow, signLaurent_qi, signLaurent_norm,
    SuperCartanDatum.pii, signLaurent_pi]

/-- Coefficient compatibility after multiplication by any covering-ring value;
no graphical form identity is assumed or asserted. -/
theorem direct_mul_coeff (σ : ℚ) (hσ : σ ^ 2 = 1) (i : I) (ν : X)
    (c : Coefficients.Ring) (z : ℤ) :
    (signLaurent σ hσ (direct D i ν * c)).coeff z =
      (signLaurent σ hσ (bar (qpInt (D.qi Coefficients.q i) (D.pii pi i)
        (D.h i ν))) * signLaurent σ hσ c).coeff z := by
  rw [direct_eq_bar, map_mul]

end CapScalar
end OddMath.CoveringQuantum
