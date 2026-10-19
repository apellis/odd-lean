/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.VermaPolarization
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# A weight-parametric comparison of the actual Verma and half forms

For every word and every free-half second argument, the normalized actual
Verma polarization is evaluation of an explicit highest-weight-independent
polynomial. Its constant coefficient is the existing half pairing, and its
total degree is at most the word length. Thus the difference is a polynomial
with zero constant coefficient in pi_i^|h_i(Lambda)| q_i^(2h_i(Lambda)).

This is the algebraic precursor to CHWII Proposition 6.10, translated to the
BE2 rho / Clark IV tau1-prime convention. It proves neither q-adic convergence
nor descent to an integrable quotient, and assumes neither one.
Colours may be infinite, and bar-consistency is not required.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open PreF Coefficients
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X) (Λ : X)

/-- Every weight projector is self-adjoint for the constructed polarization. -/
theorem polarization_weightProject (μ : X) (x y : D.serreF Coefficients.q pi) :
    polarization D Λ (weightProject D Λ μ x) y =
      polarization D Λ x (weightProject D Λ μ y) := by
  have h := polarization_adjoint D Λ
    ⟨one D Coefficients.q pi μ, one_mem_modified D Coefficients.q pi μ⟩ x y
  change polarization D Λ (representation D Λ (one D Coefficients.q pi μ) x) y =
    polarization D Λ x (representation D Λ
      (rho D Coefficients.q pi pi_sq (one D Coefficients.q pi μ)).unop y) at h
  simpa only [rho_one, representation_one] using h

omit [DecidableEq I] [DecidableEq X] in
private theorem project_word (w : List I) :
    weightProject D Λ (Λ + halfWeight D false (wordWeight w))
      (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) =
      D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w) := by
  classical
  rw [weightProject_mk, weightProjectFree_monomial]
  have hf : halfWeight D false (wordWeight w) = -halfWeight D true (wordWeight w) := by
    simp [halfWeight, halfRoot, Finsupp.sum, Finset.sum_neg_distrib]
  simp [hf]

/-- Exact lowering adjointness on words, with no degree restriction on the second argument. -/
theorem polarization_word_cons (i : I) (w : List I) (y : D.serreF Coefficients.q pi) :
    polarization D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring (i :: w))) y =
      qp Coefficients.q (D.d i * (D.h i (Λ + halfWeight D false (wordWeight w)) - 1)) •
        polarization D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))
          (lower D.toSuperCartanDatum i (D.h i Λ) y) := by
  let μ := Λ + halfWeight D false (wordWeight w)
  rw [polarization_apply, halfMap_monomial, halfWord,
    rho_mul]
  simp only [halfGen, Bool.false_eq_true, ite_false]
  rw [rho_F, map_mul, Module.End.mul_apply, map_smul, LinearMap.smul_apply,
    representation_E, map_smul, map_smul]
  rw [Module.End.mul_apply, ← weightProject_lower]
  rw [← halfMap_monomial]
  change _ • polarization D Λ
    (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))
      (weightProject D Λ μ (lower D.toSuperCartanDatum i (D.h i Λ) y)) = _
  rw [← polarization_weightProject, project_word]

/-- An explicitly constructed deformation, not an assumed polarization. -/
def wordDeformation (t : I → Coefficients.Ring) : List I →
    PreF Coefficients.Ring I →ₗ[Coefficients.Ring] Coefficients.Ring
  | [] => counit.toLinearMap
  | i :: w =>
    (D.norm Coefficients.q pi i *
      ((D.qi Coefficients.q i ^ (-D.h i (halfWeight D true (wordWeight w))) :
        Coefficients.Ringˣ) : Coefficients.Ring)) •
      ((wordDeformation t w).comp
        ((weightTwist D.toSuperCartanDatum Coefficients.q i).toLinearMap.comp
          (lDeriv (D.chi Coefficients.q pi) i)) -
        t i • (wordDeformation t w).comp
          ((parityTwist D.toSuperCartanDatum pi i).toLinearMap.comp
            (rDeriv (D.chi Coefficients.q pi) i)))

omit [DecidableEq X] in
/-- At zero deformation, the formula is EXACTLY the existing half form on all words. -/
theorem wordDeformation_zero (w : List I) (y : PreF Coefficients.Ring I) :
    wordDeformation D (fun _ ↦ 0) w y =
      D.form Coefficients.q pi (monomial Coefficients.Ring w) y := by
  induction w generalizing y with
  | nil => simp [wordDeformation, SuperCartanDatum.form]
  | cons i w ih =>
    simp only [wordDeformation, LinearMap.smul_apply, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, zero_smul, sub_zero, ih]
    have ht (z : PreF Coefficients.Ring I) :
        D.form Coefficients.q pi (weightTwist D.toSuperCartanDatum Coefficients.q i
          (monomial Coefficients.Ring w)) z =
        D.form Coefficients.q pi (monomial Coefficients.Ring w)
          (weightTwist D.toSuperCartanDatum Coefficients.q i z) :=
      form_diagTwist _ _ _ _ _
    rw [← ht, weightTwist_monomial, map_smul, SuperCartanDatum.form,
      monomial_cons, form_θ_mul]
    change (D.norm Coefficients.q pi i * _) * (_ * _) = _ * _
    rw [← mul_assoc]
    congr 1
    rw [mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, mul_one]

/-- Highest-weight parameters; the q-exponent is explicit and grows with the weight. -/
def deformationParameter (i : I) : Coefficients.Ring :=
  D.pii pi i ^ (D.h i Λ).natAbs *
    ((D.qi Coefficients.q i ^ (2 * D.h i Λ) : Coefficients.Ringˣ) : Coefficients.Ring)

/-- The pi-sign required by rho/tau1-prime, as opposed to CHWII's tau1. -/
def polarizationSign (i : I) : Coefficients.Ring :=
  D.pii pi i * D.pii pi i ^ (D.h i Λ).natAbs

/-- The total pi-sign of a word. -/
def wordSign (w : List I) : Coefficients.Ring := (w.map (polarizationSign D Λ)).prod

omit [DecidableEq I] [DecidableEq X] in
private theorem inverse_denominator (i : I) :
    Ring.inverse (vermaDenominator D.toSuperCartanDatum Coefficients.q pi i) =
      -(D.pii pi i * (D.qi Coefficients.q i : Coefficients.Ring)) *
        D.norm Coefficients.q pi i := by
  apply (vermaDenominator_isUnit D.toSuperCartanDatum i).mul_left_cancel
  rw [Ring.mul_inverse_cancel _ (vermaDenominator_isUnit D.toSuperCartanDatum i)]
  have hf : vermaDenominator D.toSuperCartanDatum Coefficients.q pi i *
      (-(D.pii pi i * (D.qi Coefficients.q i : Coefficients.Ring))) =
      1 - D.pii pi i * (D.qi Coefficients.q i : Coefficients.Ring) ^ 2 := by
    dsimp [vermaDenominator]
    have hp := D.pii_sq pi pi_sq i
    have hu := Units.inv_mul (D.qi Coefficients.q i)
    calc
      _ = D.pii pi i ^ 2 *
          (((D.qi Coefficients.q i)⁻¹ : Coefficients.Ringˣ) : Coefficients.Ring) *
          (D.qi Coefficients.q i : Coefficients.Ring) -
          D.pii pi i * (D.qi Coefficients.q i : Coefficients.Ring) ^ 2 := by ring
      _ = _ := by rw [hp, one_mul, hu]
  rw [← mul_assoc, hf, denominator_mul_norm]

omit [DecidableEq X] in
private theorem scaled_lowerFree (i : I) (m : ℤ) (y : PreF Coefficients.Ring I) :
    ((D.qi Coefficients.q i ^ (D.h i Λ - m - 1) : Coefficients.Ringˣ) : Coefficients.Ring) •
      lowerFree D.toSuperCartanDatum Coefficients.q pi i (D.h i Λ) y =
    (polarizationSign D Λ i * D.norm Coefficients.q pi i *
      ((D.qi Coefficients.q i ^ (-m) : Coefficients.Ringˣ) : Coefficients.Ring)) •
      (weightTwist D.toSuperCartanDatum Coefficients.q i (lDeriv (D.chi Coefficients.q pi) i y) -
        deformationParameter D Λ i •
          parityTwist D.toSuperCartanDatum pi i (rDeriv (D.chi Coefficients.q pi) i y)) := by
  have hp : (D.pii pi i ^ (D.h i Λ).natAbs) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm _ 2, pow_mul, D.pii_sq pi pi_sq, one_pow]
  have he (a b : ℤ) :
      ((D.qi Coefficients.q i ^ a : Coefficients.Ringˣ) : Coefficients.Ring) *
        ((D.qi Coefficients.q i ^ b : Coefficients.Ringˣ) : Coefficients.Ring) =
      ((D.qi Coefficients.q i ^ (a + b) : Coefficients.Ringˣ) : Coefficients.Ring) := by
    rw [← Units.val_mul, ← zpow_add]
  have heone (a : ℤ) :
      ((D.qi Coefficients.q i ^ a : Coefficients.Ringˣ) : Coefficients.Ring) *
        (D.qi Coefficients.q i : Coefficients.Ring) =
      ((D.qi Coefficients.q i ^ (a + 1) : Coefficients.Ringˣ) : Coefficients.Ring) := by
    simpa only [zpow_one] using he a 1
  have ha :
      ((D.qi Coefficients.q i ^ (D.h i Λ - m - 1) : Coefficients.Ringˣ) : Coefficients.Ring) *
        (D.qi Coefficients.q i : Coefficients.Ring) *
        ((D.qi Coefficients.q i ^ D.h i Λ : Coefficients.Ringˣ) : Coefficients.Ring) =
      ((D.qi Coefficients.q i ^ (-m) : Coefficients.Ringˣ) : Coefficients.Ring) *
        ((D.qi Coefficients.q i ^ (2 * D.h i Λ) : Coefficients.Ringˣ) : Coefficients.Ring) := by
    rw [heone, he, he]
    congr 2; ring
  have hb :
      ((D.qi Coefficients.q i ^ (D.h i Λ - m - 1) : Coefficients.Ringˣ) : Coefficients.Ring) *
        (D.qi Coefficients.q i : Coefficients.Ring) *
        ((D.qi Coefficients.q i ^ (-D.h i Λ) : Coefficients.Ringˣ) : Coefficients.Ring) =
      ((D.qi Coefficients.q i ^ (-m) : Coefficients.Ringˣ) : Coefficients.Ring) := by
    rw [heone, he]
    congr 2; ring
  simp only [lowerFree, lowerNumerator, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, inverse_denominator, smul_sub,
    smul_smul, polarizationSign, deformationParameter]
  have hca :
      ((D.qi Coefficients.q i ^ (D.h i Λ - m - 1) : Coefficients.Ringˣ) : Coefficients.Ring) *
        (-(D.pii pi i * (D.qi Coefficients.q i : Coefficients.Ring)) * D.norm Coefficients.q pi i) *
        ((D.qi Coefficients.q i ^ D.h i Λ : Coefficients.Ringˣ) : Coefficients.Ring) =
      -(D.pii pi i * D.pii pi i ^ (D.h i Λ).natAbs * D.norm Coefficients.q pi i *
        ((D.qi Coefficients.q i ^ (-m) : Coefficients.Ringˣ) : Coefficients.Ring) *
        (D.pii pi i ^ (D.h i Λ).natAbs *
          ((D.qi Coefficients.q i ^ (2 * D.h i Λ) : Coefficients.Ringˣ) : Coefficients.Ring))) := by
    linear_combination -(D.pii pi i * D.norm Coefficients.q pi i) * ha +
      D.pii pi i * D.norm Coefficients.q pi i *
        ((D.qi Coefficients.q i ^ (-m) : Coefficients.Ringˣ) : Coefficients.Ring) *
        ((D.qi Coefficients.q i ^ (2 * D.h i Λ) : Coefficients.Ringˣ) : Coefficients.Ring) * hp
  have hcb :
      ((D.qi Coefficients.q i ^ (D.h i Λ - m - 1) : Coefficients.Ringˣ) : Coefficients.Ring) *
        (-(D.pii pi i * (D.qi Coefficients.q i : Coefficients.Ring)) * D.norm Coefficients.q pi i) *
        (D.pii pi i ^ (D.h i Λ).natAbs *
          ((D.qi Coefficients.q i ^ (-D.h i Λ) : Coefficients.Ringˣ) : Coefficients.Ring)) =
      -(D.pii pi i * D.pii pi i ^ (D.h i Λ).natAbs * D.norm Coefficients.q pi i *
        ((D.qi Coefficients.q i ^ (-m) : Coefficients.Ringˣ) : Coefficients.Ring)) := by
    linear_combination
      -(D.pii pi i * D.pii pi i ^ (D.h i Λ).natAbs * D.norm Coefficients.q pi i) * hb
  simp only [← mul_assoc] at hca hcb ⊢
  rw [hca, hcb]
  simp only [neg_smul, sub_eq_add_neg, neg_neg]
  exact add_comm _ _

/-- Exact comparison on arbitrary words and arbitrary second arguments.
The same explicit deformation has zero value equal to the half form. -/
theorem polarization_word_deformation (w : List I) (y : PreF Coefficients.Ring I) :
    polarization D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))
      (D.toSerreF Coefficients.q pi y) =
      wordSign D Λ w * wordDeformation D (deformationParameter D Λ) w y := by
  induction w generalizing y with
  | nil => simp only [monomial_nil, map_one, polarization_one_left, constant_mk,
      wordSign, List.map_nil, List.prod_nil, one_mul, wordDeformation, AlgHom.toLinearMap_apply]
  | cons i w ih =>
    rw [polarization_word_cons, lower_mk, ← map_smul, ← map_smul]
    have hf : halfWeight D false (wordWeight w) = -halfWeight D true (wordWeight w) := by
      simp [halfWeight, halfRoot, Finsupp.sum, Finset.sum_neg_distrib]
    have hq : qp Coefficients.q
        (D.d i * (D.h i (Λ + halfWeight D false (wordWeight w)) - 1)) =
        ((D.qi Coefficients.q i ^ (D.h i Λ - D.h i (halfWeight D true (wordWeight w)) - 1) :
          Coefficients.Ringˣ) : Coefficients.Ring) := by
      simp only [hf, ← sub_eq_add_neg, map_sub, qp, SuperCartanDatum.qi,
        zpow_mul, zpow_natCast]
    rw [hq, scaled_lowerFree, map_smul, map_smul, map_sub, map_sub, map_smul, map_smul, ih, ih]
    simp only [wordSign, List.map_cons, List.prod_cons, wordDeformation, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, smul_eq_mul]
    ring

/-- The comparison polynomial is independent of the highest weight.
Its coefficients are in the actual generic covering ring, not a field replacement. -/
def wordPolynomial : List I → PreF Coefficients.Ring I → MvPolynomial I Coefficients.Ring
  | [], y => MvPolynomial.C (counit y)
  | i :: w, y => MvPolynomial.C (D.norm Coefficients.q pi i *
      ((D.qi Coefficients.q i ^ (-D.h i (halfWeight D true (wordWeight w))) :
        Coefficients.Ringˣ) : Coefficients.Ring)) *
      (wordPolynomial w (weightTwist D.toSuperCartanDatum Coefficients.q i
        (lDeriv (D.chi Coefficients.q pi) i y)) -
        MvPolynomial.X i * wordPolynomial w (parityTwist D.toSuperCartanDatum pi i
          (rDeriv (D.chi Coefficients.q pi) i y)))

omit [DecidableEq X] in
theorem wordPolynomial_eval (t : I → Coefficients.Ring) (w : List I)
    (y : PreF Coefficients.Ring I) :
    MvPolynomial.eval t (wordPolynomial D w y) = wordDeformation D t w y := by
  induction w generalizing y with
  | nil => simp [wordPolynomial, wordDeformation]
  | cons i w ih => simp [wordPolynomial, wordDeformation, ih, smul_eq_mul]

omit [DecidableEq X] in
/-- The constant term is the existing half form, on arbitrary words. -/
theorem wordPolynomial_constantCoeff (w : List I) (y : PreF Coefficients.Ring I) :
    MvPolynomial.constantCoeff (wordPolynomial D w y) =
      D.form Coefficients.q pi (monomial Coefficients.Ring w) y := by
  rw [← MvPolynomial.eval_zero', wordPolynomial_eval, wordDeformation_zero]

omit [DecidableEq X] in
/-- A real polynomial degree bound; this is NOT a claim about q-valuation. -/
theorem wordPolynomial_totalDegree (w : List I) (y : PreF Coefficients.Ring I) :
    (wordPolynomial D w y).totalDegree ≤ w.length := by
  induction w generalizing y with
  | nil => simp [wordPolynomial]
  | cons i w ih =>
    simp only [wordPolynomial, List.length_cons]
    apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_C, zero_add]
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · exact (ih _).trans (Nat.le_succ _)
    · apply (MvPolynomial.totalDegree_mul _ _).trans
      rw [MvPolynomial.totalDegree_X]
      exact (Nat.add_le_add_left (ih _) 1).trans_eq (Nat.add_comm 1 _)

/-- Highest-weight comparison, with an explicit polynomial and its half-form constant term.
Together with `wordPolynomial_totalDegree`, this is the finite algebraic ingredient
for a q-adic limit, not the limit or nondegeneracy itself. -/
theorem polarization_word_polynomial (w : List I) (y : PreF Coefficients.Ring I) :
    polarization D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))
      (D.toSerreF Coefficients.q pi y) = wordSign D Λ w *
        MvPolynomial.eval (deformationParameter D Λ) (wordPolynomial D w y) := by
  rw [wordPolynomial_eval, polarization_word_deformation]

omit [DecidableEq I] [DecidableEq X] in
/-- The normalization sign is a unit even though the covering ring has zero divisors. -/
theorem wordSign_sq (w : List I) : wordSign D Λ w ^ 2 = 1 := by
  induction w with
  | nil => simp [wordSign]
  | cons i w ih =>
    have hp : (D.pii pi i ^ (D.h i Λ).natAbs) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm _ 2, pow_mul, D.pii_sq pi pi_sq, one_pow]
    change (polarizationSign D Λ i * wordSign D Λ w) ^ 2 = 1
    rw [mul_pow, ih, mul_one, polarizationSign, mul_pow, D.pii_sq pi pi_sq, hp, one_mul]

/-- The weight-independent error polynomial after subtracting the existing half form. -/
def comparisonError (w : List I) (y : PreF Coefficients.Ring I) :
    MvPolynomial I Coefficients.Ring := wordPolynomial D w y -
      MvPolynomial.C (D.form Coefficients.q pi (monomial Coefficients.Ring w) y)

omit [DecidableEq X] in
theorem comparisonError_constantCoeff (w : List I) (y : PreF Coefficients.Ring I) :
    MvPolynomial.constantCoeff (comparisonError D w y) = 0 := by
  simp [comparisonError, wordPolynomial_constantCoeff]

omit [DecidableEq X] in
theorem comparisonError_totalDegree (w : List I) (y : PreF Coefficients.Ring I) :
    (comparisonError D w y).totalDegree ≤ w.length :=
  (MvPolynomial.totalDegree_sub_C_le _ _).trans (wordPolynomial_totalDegree D w y)

/-- Actual normalized polarization minus the half form is a bounded-degree polynomial
with ZERO constant coefficient, evaluated at explicit highest-weight parameters.
This is a comparison theorem on arbitrary words, not a filtration recurrence. -/
theorem polarization_sub_half (w : List I) (y : PreF Coefficients.Ring I) :
    wordSign D Λ w *
      polarization D Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))
        (D.toSerreF Coefficients.q pi y) -
      D.serreForm Coefficients.q pi pi_sq
        (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))
        (D.toSerreF Coefficients.q pi y) =
      MvPolynomial.eval (deformationParameter D Λ) (comparisonError D w y) := by
  rw [polarization_word_polynomial, ← mul_assoc, ← pow_two, wordSign_sq, one_mul,
    SuperCartanDatum.serreForm_toSerreF]
  simp [comparisonError, SuperCartanDatum.form]

end OddMath.CoveringQuantum.UDot.GenericVerma
