/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerNorm
import Mathlib.Algebra.Polynomial.Monic

/-! # Monic normalized endpoint norm polynomials

The independent moving-chain norm factors have the prescribed scalar unit leading
coefficients over any possibly noncommutative coefficient ring. Their ordered
normalized product is monic. `EndpointNormEvaluation` evaluates this polynomial
on actual affine dots; neither norm cancellation in a cyclotomic quotient nor
bounded cyclotomic support is inferred from monicity alone.
-/

noncomputable section
open scoped Classical
open Polynomial
namespace OddMath.QuiverHecke
open IntertwinerMeet
universe u v
variable {I k : Type u} {L : Type v} [AddCommGroup L]
  (D : SKM.Datum I L) [CommRing k] (Sc : SKM.Scalars D k)
variable {B : Type*} [Ring B] [Algebra k B]

theorem qLeft_polynomial_leadingCoeff (u : B) (d e : ℕ) (he : 0 < e)
    (t₁ : k) (t₂ : kˣ) (s : ℕ → ℕ → k) :
    (qLeft (C u) (X : Polynomial B) d e t₁ (t₂ : k) s).leadingCoeff =
      algebraMap k B (t₂ : k) := by
  nontriviality B
  have ht : algebraMap k B (t₂ : k) ≠ 0 := (t₂.isUnit.map (algebraMap k B)).ne_zero
  have hlow : (∑ p ∈ Finset.Ioo 0 d, ∑ q ∈ Finset.Ioo 0 e,
      s p q • ((C u : Polynomial B) ^ p * X ^ q)).degree < (e : WithBot ℕ) := by
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (by simp)).mpr
    intro p hp
    apply (degree_sum_le _ _).trans_lt
    apply (Finset.sup_lt_iff (by simp)).mpr
    intro q hq
    apply lt_of_le_of_lt (degree_smul_le _ _)
    rw [← map_pow]
    exact (degree_C_mul_X_pow_le q (u ^ p)).trans_lt
      (WithBot.coe_lt_coe.mpr (Finset.mem_Ioo.mp hq).2)
  have hconst : ((t₁ • (C u : Polynomial B) ^ d)).degree < (e : WithBot ℕ) := by
    apply lt_of_le_of_lt (degree_smul_le _ _)
    rw [← map_pow]
    exact degree_C_le.trans_lt (WithBot.coe_lt_coe.mpr he)
  have htop : (t₂.val • (X : Polynomial B) ^ e) =
      C (algebraMap k B t₂.val) * X ^ e := by
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  unfold qLeft
  rw [← add_assoc, htop, leadingCoeff_add_of_degree_lt]
  · simp
  · rw [degree_C_mul_X_pow e ht]
    exact (degree_add_le _ _).trans_lt (max_lt hlow hconst)

theorem endpointNormFactor_polynomial_isUnit_leadingCoeff (j i : I) (u : B) :
    IsUnit (endpointNormFactor D Sc j i (C u) (X : Polynomial B)).leadingCoeff := by
  unfold endpointNormFactor
  split_ifs with hji hp hd
  · have hm : (((X : Polynomial B) ^ 2 - C u ^ 2) ^ 2 *
        (C u ^ 2 + X ^ 2)).Monic := by
      apply Monic.mul
      · apply Monic.pow
        simpa only [← map_pow] using
          (monic_X_pow_sub_C (u ^ 2) (by decide : (2 : ℕ) ≠ 0))
      · simpa only [← map_pow, add_comm] using
          (monic_X_pow_add_C (u ^ 2) (by decide : (2 : ℕ) ≠ 0))
    rw [leadingCoeff_neg, hm.leadingCoeff]
    exact isUnit_one.neg
  · have hm : (((X : Polynomial B) - C u) ^ 2).Monic :=
      (monic_X_sub_C u).pow 2
    rw [leadingCoeff_neg, hm.leadingCoeff]
    exact isUnit_one.neg
  · simpa only [Polynomial.algebraMap_apply, leadingCoeff_C] using
      (Sc.t j i).isUnit.map (algebraMap k B)
  · have he : 0 < D.dn i j := by
      have hc := D.dn_cast (Ne.symm hji)
      have hz : D.d i j ≠ 0 := fun hz => hd ((D.d_eq_zero_iff j i).mpr hz)
      omega
    rw [qLeft_polynomial_leadingCoeff u _ _ he]
    exact (Sc.t i j).isUnit.map (algebraMap k B)

/-- The literal leading scalar: diagonal minus sign, or the appropriate t unit. -/
def endpointNormLeadingUnit (j i : I) : kˣ :=
  if j = i then -1 else if D.d j i = 0 then Sc.t j i else Sc.t i j

theorem endpointNormFactor_polynomial_leadingCoeff (j i : I) (u : B) :
    (endpointNormFactor D Sc j i (C u) (X : Polynomial B)).leadingCoeff =
      algebraMap k B (endpointNormLeadingUnit D Sc j i : k) := by
  unfold endpointNormFactor endpointNormLeadingUnit
  split_ifs with hji hp hd
  · have hm : (((X : Polynomial B) ^ 2 - C u ^ 2) ^ 2 *
        (C u ^ 2 + X ^ 2)).Monic := by
      apply Monic.mul
      · apply Monic.pow
        simpa only [← map_pow] using
          (monic_X_pow_sub_C (u ^ 2) (by decide : (2 : ℕ) ≠ 0))
      · simpa only [← map_pow, add_comm] using
          (monic_X_pow_add_C (u ^ 2) (by decide : (2 : ℕ) ≠ 0))
    simp [leadingCoeff_neg, hm.leadingCoeff]
  · have hm : (((X : Polynomial B) - C u) ^ 2).Monic :=
      (monic_X_sub_C u).pow 2
    simp [leadingCoeff_neg, hm.leadingCoeff]
  · simp only [Polynomial.algebraMap_apply, leadingCoeff_C]
  · have he : 0 < D.dn i j := by
      have hc := D.dn_cast (Ne.symm hji)
      have hz : D.d i j ≠ 0 := fun hz => hd ((D.d_eq_zero_iff j i).mpr hz)
      omega
    exact qLeft_polynomial_leadingCoeff u _ _ he _ _ _

/-- Left normalization by the explicit inverse sign/t unit. -/
def normalizedEndpointNormFactor (j i : I) (u : B) : Polynomial B :=
  C (algebraMap k B ((endpointNormLeadingUnit D Sc j i)⁻¹ : kˣ)) *
    endpointNormFactor D Sc j i (C u) X

theorem normalizedEndpointNormFactor_monic (j i : I) (u : B) :
    (normalizedEndpointNormFactor D Sc j i u).Monic := by
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [endpointNormFactor_polynomial_leadingCoeff, ← map_mul]
  simp

/-- Ordered normalized product; no commutativity of the coefficient ring is used. -/
def normalizedEndpointNormPolynomial (i : I) : List (I × B) → Polynomial B
  | [] => 1
  | (j, u) :: xs => normalizedEndpointNormFactor D Sc j i u *
      normalizedEndpointNormPolynomial i xs

theorem normalizedEndpointNormPolynomial_monic (i : I) (xs : List (I × B)) :
    (normalizedEndpointNormPolynomial D Sc i xs).Monic := by
  induction xs with
  | nil => exact monic_one
  | cons x xs ih =>
    exact (normalizedEndpointNormFactor_monic D Sc x.1 i x.2).mul ih

end OddMath.QuiverHecke
