/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.UDot.TensorGram.Transport

/-!
# Finite generator formulas for the normalized tensor Gram

Exact coefficient-bar, deformation and mixed-generator identities for the
actual transported form on dominant highest/lowest quotient tensors.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.PolarizationTransport
open Coefficients PreF TensorProduct GenericVerma
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

omit [DecidableEq I] [DecidableEq X] in
/-- Bar on the actual half norm over the covering RING, not a field argument. -/
theorem bar_norm (i : I) : bar (D.norm Coefficients.q pi i) =
    -(D.pii pi i * qp Coefficients.q (2 * D.d i) * D.norm Coefficients.q pi i) := by
  have h1 := denominator_mul_norm D.toSuperCartanDatum i
  have hq : ((D.qi Coefficients.q i : Coefficients.Ringˣ) : Coefficients.Ring) ^ 2 =
      qp Coefficients.q (2 * D.d i) := by
    rw [show (2 * (D.d i : ℤ)) = D.d i + D.d i by ring, ← qp_mul]
    simp [qp, SuperCartanDatum.qi, pow_two]
  rw [hq] at h1
  have h2 := congrArg bar h1
  simp only [map_mul, map_sub, map_one, barData.map_pii, barData.map_qp] at h2
  have h3 : qp Coefficients.q (2 * D.d i) * qp Coefficients.q (-(2 * D.d i)) = 1 := by
    rw [qp_mul, add_neg_cancel, qp_zero]
  have he := D.pii_sq pi pi_sq i
  linear_combination
    -bar (D.norm Coefficients.q pi i) * h1 -
    D.pii pi i * qp Coefficients.q (2 * D.d i) * D.norm Coefficients.q pi i * h2 -
    D.norm Coefficients.q pi i * bar (D.norm Coefficients.q pi i) * h3 -
    qp Coefficients.q (2 * D.d i) * qp Coefficients.q (-(2 * D.d i)) *
      D.norm Coefficients.q pi i * bar (D.norm Coefficients.q pi i) * he

omit [DecidableEq I] [DecidableEq X] in
theorem deformation_eq_qp (Λ : X) (i : I) : deformationParameter D Λ i =
    D.pii pi i ^ (D.h i Λ).natAbs * qp Coefficients.q (2 * D.d i * D.h i Λ) := by
  simp only [deformationParameter, SuperCartanDatum.qi, qp, ← zpow_natCast, ← zpow_mul]
  congr 3
  ring

omit [DecidableEq I] [DecidableEq X] in
theorem bar_deformation (Λ : X) (i : I) : bar (deformationParameter D Λ i) =
    D.pii pi i ^ (D.h i Λ).natAbs * qp Coefficients.q (-(2 * D.d i * D.h i Λ)) := by
  simp only [deformation_eq_qp, map_mul, map_pow, barData.map_pii, barData.map_qp]

omit [DecidableEq I] [DecidableEq X] in
theorem parl_difference (Λ Μ : X) (i : I) :
    pi ^ (D.parl i (Λ - Μ)).val =
      D.pii pi i * D.pii pi i ^ (D.h i Λ).natAbs * D.pii pi i ^ (D.h i Μ).natAbs := by
  rw [pow_parl pi_sq, sub_eq_add_neg, tensor_pii_abs_add]
  simp only [RootDatum.h, map_sub, Int.natAbs_neg, Int.natAbs_one, pow_one]
  rw [sub_eq_add_neg, tensor_pii_abs_add]
  simp only [Int.natAbs_neg]
  ring

omit [DecidableEq I] [DecidableEq X] in
theorem qi_zpow (i : I) (n : ℤ) :
    ((D.qi Coefficients.q i ^ n : Coefficients.Ringˣ) : Coefficients.Ring) =
      qp Coefficients.q (D.d i * n) := by
  simp [SuperCartanDatum.qi, qp, ← zpow_natCast, ← zpow_mul]

omit [DecidableEq I] [DecidableEq X] in
/-- The fixed-difference quantum integer supplies the missing leading F scalar. -/
theorem qint_normalized (μ : X) (i : I) :
    qp Coefficients.q (D.d i * (D.h i μ - 1)) *
      qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i μ) =
    pi ^ (D.parl i μ).val * D.norm Coefficients.q pi i -
      D.pii pi i * qp Coefficients.q (2 * D.d i * D.h i μ) * D.norm Coefficients.q pi i := by
  have hd := denominator_qpInt D Coefficients.q pi pi_sq i (D.h i μ)
  rw [qi_zpow, qi_zpow] at hd
  have hn := denominator_mul_norm D.toSuperCartanDatum i
  have hq : ((D.qi Coefficients.q i : Coefficients.Ringˣ) : Coefficients.Ring) =
      qp Coefficients.q (D.d i) := by simp [SuperCartanDatum.qi, qp]
  have hqi : (((D.qi Coefficients.q i)⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring) =
      qp Coefficients.q (-D.d i) := by
    simpa only [zpow_neg_one, mul_neg_one] using qi_zpow D i (-1)
  have hc : (-D.pii pi i * qp Coefficients.q (D.d i) * D.norm Coefficients.q pi i) *
      vermaDenominator D.toSuperCartanDatum Coefficients.q pi i = 1 := by
    rw [vermaDenominator, hq, hqi]
    have he := D.pii_sq pi pi_sq i
    have hu : qp Coefficients.q (D.d i) * qp Coefficients.q (-D.d i) = 1 := by
      rw [qp_mul, add_neg_cancel, qp_zero]
    rw [hq] at hn
    linear_combination hn +
      D.norm Coefficients.q pi i * hu +
      qp Coefficients.q (D.d i) * qp Coefficients.q (-D.d i) *
        D.norm Coefficients.q pi i * he
  have hi : qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i μ) =
      (-D.pii pi i * qp Coefficients.q (D.d i) * D.norm Coefficients.q pi i) *
        (qp Coefficients.q (D.d i * D.h i μ) -
          D.pii pi i ^ (D.h i μ).natAbs * qp Coefficients.q (D.d i * -D.h i μ)) := by
    rw [← hd, ← mul_assoc, hc, one_mul]
  have hp : pi ^ (D.parl i μ).val = D.pii pi i * D.pii pi i ^ (D.h i μ).natAbs := by
    simpa only [neg_neg, RootDatum.h, map_neg, Int.natAbs_neg] using clarkOmega_coefficient D i (-μ)
  rw [hi, hp]
  have hplus : qp Coefficients.q (D.d i * (D.h i μ - 1)) *
      qp Coefficients.q (D.d i) * qp Coefficients.q (D.d i * D.h i μ) =
      qp Coefficients.q (2 * D.d i * D.h i μ) := by
    rw [qp_mul, qp_mul]
    congr 1
    ring
  have hminus : qp Coefficients.q (D.d i * (D.h i μ - 1)) *
      qp Coefficients.q (D.d i) * qp Coefficients.q (D.d i * -D.h i μ) = 1 := by
    rw [qp_mul, qp_mul, show D.d i * (D.h i μ - 1) + D.d i + D.d i * -D.h i μ = 0 by ring,
      qp_zero]
  calc
    _ = D.pii pi i * D.pii pi i ^ (D.h i μ).natAbs * D.norm Coefficients.q pi i *
        (qp Coefficients.q (D.d i * (D.h i μ - 1)) *
          qp Coefficients.q (D.d i) * qp Coefficients.q (D.d i * -D.h i μ)) -
      D.pii pi i * D.norm Coefficients.q pi i *
        (qp Coefficients.q (D.d i * (D.h i μ - 1)) *
          qp Coefficients.q (D.d i) * qp Coefficients.q (D.d i * D.h i μ)) := by ring
    _ = _ := by rw [hplus, hminus]; ring

variable [Finite I] (hD : D.toSuperCartanDatum.BarConsistent) (Λ Μ : X)

@[simp] theorem project_vac : tensorProject D hD Λ Μ (Λ - Μ) (vac D hD Λ Μ) =
    vac D hD Λ Μ := by
  have h := tensorProject_tmul_word D hD Λ Μ (Λ - Μ) (toIntegrable D hD Λ 1) []
  simpa [vac, integrableRepresentation_toIntegrable, representation_one,
    weightProject_mk, weightProjectFree_monomial] using h

@[simp] theorem E_vac (s : Bool) (i : I) :
    tensorRepresentation D hD Λ Μ s (E D Coefficients.q pi i (Λ - Μ))
      (vac D hD Λ Μ) = tensorE D hD Λ Μ s i (vac D hD Λ Μ) := by
  simp [tensorEBlock]

@[simp] theorem F_vac (s : Bool) (i : I) :
    tensorRepresentation D hD Λ Μ s (F D Coefficients.q pi i (Λ - Μ))
      (vac D hD Λ Μ) = tensorF D hD Λ Μ s i (vac D hD Λ Μ) := by
  simp

/-- Exact finite E Gram, with NO growing-weight Laurent prefactor remaining. -/
theorem gram_E (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) (s : Bool) (i : I) :
    gram D hD Λ Μ hΛ hΜ s (E D Coefficients.q pi i (Λ - Μ))
      (E D Coefficients.q pi i (Λ - Μ)) =
        D.norm Coefficients.q pi i * (1 - deformationParameter D Μ i) := by
  rw [gram_apply, left_E, right_E]
  simp only [map_smul, LinearMap.smul_apply, E_vac,
    MixedGram.E_cross_gram, smul_eq_mul, map_mul, map_pow, barData.map_qp,
    barData.map_pii, map_sub, map_one, bar_norm, bar_deformation, parl_difference]
  have he := D.pii_sq pi pi_sq i
  have hj : (D.pii pi i ^ (D.h i Λ).natAbs) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm _ 2, pow_mul, he, one_pow]
  have hk : (D.pii pi i ^ (D.h i Μ).natAbs) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm _ 2, pow_mul, he, one_pow]
  have hq : qp Coefficients.q (-(D.d i * (D.h i (Λ - Μ) + 1))) ^ 2 *
      qp Coefficients.q (D.d i * D.h i Λ) ^ 2 * qp Coefficients.q (2 * D.d i) =
      qp Coefficients.q (2 * D.d i * D.h i Μ) := by
    simp only [pow_two, qp_mul]
    congr 1
    simp only [RootDatum.h, map_sub]
    ring
  have hq' : qp Coefficients.q (2 * D.d i * D.h i Μ) *
      qp Coefficients.q (-(2 * D.d i * D.h i Μ)) = 1 := by
    rw [qp_mul, add_neg_cancel, qp_zero]
  simp only [neg_neg]
  calc
    _ = -(D.pii pi i ^ 2 * (D.pii pi i ^ (D.h i Λ).natAbs) ^ 2) *
      D.pii pi i ^ (D.h i Μ).natAbs *
      (qp Coefficients.q (-(D.d i * (D.h i (Λ - Μ) + 1))) ^ 2 *
        qp Coefficients.q (D.d i * D.h i Λ) ^ 2 * qp Coefficients.q (2 * D.d i)) *
      D.norm Coefficients.q pi i *
      (1 - D.pii pi i ^ (D.h i Μ).natAbs *
        qp Coefficients.q (-(2 * D.d i * D.h i Μ))) := by
      simp only [RootDatum.h, map_sub]
      ring
    _ = D.norm Coefficients.q pi i *
        ((D.pii pi i ^ (D.h i Μ).natAbs) ^ 2 *
          (qp Coefficients.q (2 * D.d i * D.h i Μ) *
            qp Coefficients.q (-(2 * D.d i * D.h i Μ))) -
          D.pii pi i ^ (D.h i Μ).natAbs * qp Coefficients.q (2 * D.d i * D.h i Μ)) := by
      rw [he, hj, hq]
      ring
    _ = _ := by
      rw [hk, hq']
      simp only [one_mul, deformation_eq_qp]

@[simp] theorem gram_one (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) (s : Bool) :
    gram D hD Λ Μ hΛ hΜ s (one D Coefficients.q pi (Λ - Μ))
      (one D Coefficients.q pi (Λ - Μ)) = 1 := by
  simp only [gram_apply, left_one, right_one, tensorRepresentation_one, project_vac]
  simp [vac]

/-- The mixed FE scalar is retained, now with only a fixed-difference prefactor. -/
theorem gram_FE (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) (s : Bool) (i : I) :
    gram D hD Λ Μ hΛ hΜ s (one D Coefficients.q pi (Λ - Μ))
      (F D Coefficients.q pi i (Λ - Μ + D.α i) * E D Coefficients.q pi i (Λ - Μ)) =
        qp Coefficients.q (D.d i * (D.h i (Λ - Μ) + 1)) *
          (D.norm Coefficients.q pi i * (1 - deformationParameter D Μ i)) := by
  have h := gram_adjoint D hD Λ Μ hΛ hΜ s (E D Coefficients.q pi i (Λ - Μ))
    (one D Coefficients.q pi (Λ - Μ)) (E D Coefficients.q pi i (Λ - Μ))
  rw [E_mul_one_self, rho_E, smul_mul_assoc, map_smul, smul_eq_mul] at h
  calc
    _ = qp Coefficients.q (D.d i * (D.h i (Λ - Μ) + 1)) *
        gram D hD Λ Μ hΛ hΜ s (E D Coefficients.q pi i (Λ - Μ))
          (E D Coefficients.q pi i (Λ - Μ)) := by
      rw [h, ← mul_assoc, qp_mul, add_neg_cancel, qp_zero, one_mul]
    _ = _ := by rw [gram_E]

/-- ORIGINAL scalar commutator, not the false contraction-free word-length rule. -/
theorem gram_commutator (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (i : I) :
    gram D hD Λ Μ hΛ hΜ s (one D Coefficients.q pi (Λ - Μ))
      (E D Coefficients.q pi i (Λ - Μ - D.α i) * F D Coefficients.q pi i (Λ - Μ)) -
      D.pii pi i * gram D hD Λ Μ hΛ hΜ s (one D Coefficients.q pi (Λ - Μ))
        (F D Coefficients.q pi i (Λ - Μ + D.α i) * E D Coefficients.q pi i (Λ - Μ)) =
      qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i (Λ - Μ)) := by
  have h := congrArg (gram D hD Λ Μ hΛ hΜ s (one D Coefficients.q pi (Λ - Μ)))
    (comm_rel D Coefficients.q pi i i (Λ - Μ))
  have hp : D.parity i * D.parity i = D.parity i := by
    have : ∀ p : ZMod 2, p * p = p := by decide
    exact this _
  simpa only [map_sub, map_smul, smul_eq_mul, ite_true, gram_one, mul_one,
    hp, SuperCartanDatum.pii] using h

/-- Exact EF formula: the quantum integer is an indispensable scalar term. -/
theorem gram_EF (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) (s : Bool) (i : I) :
    gram D hD Λ Μ hΛ hΜ s (one D Coefficients.q pi (Λ - Μ))
      (E D Coefficients.q pi i (Λ - Μ - D.α i) * F D Coefficients.q pi i (Λ - Μ)) =
        D.pii pi i * qp Coefficients.q (D.d i * (D.h i (Λ - Μ) + 1)) *
          (D.norm Coefficients.q pi i * (1 - deformationParameter D Μ i)) +
        qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i (Λ - Μ)) := by
  have h := gram_commutator D hD Λ Μ hΛ hΜ s i
  rw [gram_FE] at h
  linear_combination h

/-- Exact F norm with the scalar contraction explicit. -/
theorem gram_F (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) (s : Bool) (i : I) :
    gram D hD Λ Μ hΛ hΜ s (F D Coefficients.q pi i (Λ - Μ))
      (F D Coefficients.q pi i (Λ - Μ)) =
      qp Coefficients.q (D.d i * (D.h i (Λ - Μ) - 1)) *
        (D.pii pi i * qp Coefficients.q (D.d i * (D.h i (Λ - Μ) + 1)) *
          (D.norm Coefficients.q pi i * (1 - deformationParameter D Μ i)) +
        qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i (Λ - Μ))) := by
  have h := gram_adjoint D hD Λ Μ hΛ hΜ s (F D Coefficients.q pi i (Λ - Μ))
    (one D Coefficients.q pi (Λ - Μ)) (F D Coefficients.q pi i (Λ - Μ))
  simpa only [F_mul_one_self, rho_F, smul_mul_assoc, map_smul, smul_eq_mul, gram_EF] using h

/-- Fixed-difference leading term and a genuine growing-weight remainder. -/
theorem gram_F_leading (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (i : I) :
    gram D hD Λ Μ hΛ hΜ s (F D Coefficients.q pi i (Λ - Μ))
      (F D Coefficients.q pi i (Λ - Μ)) =
      pi ^ (D.parl i (Λ - Μ)).val * D.norm Coefficients.q pi i -
        D.pii pi i * qp Coefficients.q (2 * D.d i * D.h i (Λ - Μ)) *
          D.norm Coefficients.q pi i * deformationParameter D Μ i := by
  rw [gram_F]
  have hq : qp Coefficients.q (D.d i * (D.h i (Λ - Μ) - 1)) *
      qp Coefficients.q (D.d i * (D.h i (Λ - Μ) + 1)) =
      qp Coefficients.q (2 * D.d i * D.h i (Λ - Μ)) := by
    rw [qp_mul]
    congr 1
    ring
  calc
    _ = qp Coefficients.q (D.d i * (D.h i (Λ - Μ) - 1)) *
        qpInt (D.qi Coefficients.q i) (D.pii pi i) (D.h i (Λ - Μ)) +
      D.pii pi i * (qp Coefficients.q (D.d i * (D.h i (Λ - Μ) - 1)) *
        qp Coefficients.q (D.d i * (D.h i (Λ - Μ) + 1))) *
        D.norm Coefficients.q pi i * (1 - deformationParameter D Μ i) := by ring
    _ = _ := by rw [qint_normalized, hq]; ring

omit [DecidableEq I] [DecidableEq X] [Finite I] in
theorem deformation_difference (i : I) :
    D.pii pi i * qp Coefficients.q (2 * D.d i * D.h i (Λ - Μ)) *
      deformationParameter D Μ i =
      pi ^ (D.parl i (Λ - Μ)).val * deformationParameter D Λ i := by
  rw [deformation_eq_qp, deformation_eq_qp, parl_difference]
  have hj : (D.pii pi i ^ (D.h i Λ).natAbs) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm _ 2, pow_mul, D.pii_sq pi pi_sq, one_pow]
  have hq : qp Coefficients.q (2 * D.d i * D.h i (Λ - Μ)) *
      qp Coefficients.q (2 * D.d i * D.h i Μ) =
      qp Coefficients.q (2 * D.d i * D.h i Λ) := by
    rw [qp_mul]
    congr 1
    simp only [RootDatum.h, map_sub]
    ring
  calc
    _ = D.pii pi i * D.pii pi i ^ (D.h i Μ).natAbs *
        (qp Coefficients.q (2 * D.d i * D.h i (Λ - Μ)) *
          qp Coefficients.q (2 * D.d i * D.h i Μ)) := by ring
    _ = _ := by rw [hq]; symm; calc
      _ = D.pii pi i * D.pii pi i ^ (D.h i Μ).natAbs *
          qp Coefficients.q (2 * D.d i * D.h i Λ) *
          (D.pii pi i ^ (D.h i Λ).natAbs) ^ 2 := by ring
      _ = _ := by rw [hj, mul_one]

/-- Exact finite F norm with the expected parity character. -/
theorem gram_F_normalized (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (i : I) :
    gram D hD Λ Μ hΛ hΜ s (F D Coefficients.q pi i (Λ - Μ))
      (F D Coefficients.q pi i (Λ - Μ)) =
      pi ^ (D.parl i (Λ - Μ)).val *
        (D.norm Coefficients.q pi i * (1 - deformationParameter D Λ i)) := by
  rw [gram_F_leading]
  have h := deformation_difference D Λ Μ i
  linear_combination -D.norm Coefficients.q pi i * h

/-- Same EF scalar in its finite normalized form. -/
theorem gram_EF_normalized (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (i : I) :
    gram D hD Λ Μ hΛ hΜ s (one D Coefficients.q pi (Λ - Μ))
      (E D Coefficients.q pi i (Λ - Μ - D.α i) * F D Coefficients.q pi i (Λ - Μ)) =
      qp Coefficients.q (-(D.d i * (D.h i (Λ - Μ) - 1))) *
        (pi ^ (D.parl i (Λ - Μ)).val *
          (D.norm Coefficients.q pi i * (1 - deformationParameter D Λ i))) := by
  have h := gram_adjoint D hD Λ Μ hΛ hΜ s (F D Coefficients.q pi i (Λ - Μ))
    (one D Coefficients.q pi (Λ - Μ)) (F D Coefficients.q pi i (Λ - Μ))
  rw [F_mul_one_self, rho_F, smul_mul_assoc, map_smul, smul_eq_mul] at h
  calc
    _ = qp Coefficients.q (-(D.d i * (D.h i (Λ - Μ) - 1))) *
        gram D hD Λ Μ hΛ hΜ s (F D Coefficients.q pi i (Λ - Μ))
          (F D Coefficients.q pi i (Λ - Μ)) := by
      rw [h, ← mul_assoc, qp_mul, neg_add_cancel, qp_zero, one_mul]
    _ = _ := by rw [gram_F_normalized]

end OddMath.CoveringQuantum.UDot.PolarizationTransport
