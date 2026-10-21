/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorGram.ToralCancellation

/-!
# Positive-word normalized tensor Gram comparison

The normalized actual Gram differs from the half form by one zero-constant
polynomial, independent of the growing weights and native coproduct choice.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.PositiveComparison
open PreF Coefficients GenericVerma MixedGram PolarizationTransport
open BarDerivatives TensorPositive Reciprocal ToralCancellation
variable {I X : Type*} [AddCommGroup X] [DecidableEq I]
variable (D : RootDatum I X)

omit [DecidableEq I] in
/-- Diagonal twists preserve the actual free root grading. -/
theorem diagTwist_mem (c : I → Coefficients.Ring) {ν : I →₀ ℕ}
    {y : PreF Coefficients.Ring I} (hy : y ∈ weightSpace Coefficients.Ring ν) :
    diagTwist c y ∈ weightSpace Coefficients.Ring ν := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [diagTwist_monomial]
    exact Submodule.smul_mem _ _ (hw ▸ monomial_mem_weightSpace w)
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

/-- The actual left derivative vanishes when the colour is absent. -/
theorem lDeriv_eq_zero (i : I) {ν : I →₀ ℕ} {y : PreF Coefficients.Ring I}
    (hν : ν i = 0) (hy : y ∈ weightSpace Coefficients.Ring ν) :
    lDeriv (D.chi Coefficients.q pi) i y = 0 := by
  have he : lDeriv (D.chi Coefficients.q pi) i y =
      twist (D.chi Coefficients.q pi) i (rDeriv (barChi D) i y) := by
    rw [inverse_rDeriv _ _ (chi_barChi D), inverse_twist _ _ (chi_barChi D)]
  rw [he, rDeriv_eq_zero_of_mem _ i hν hy, map_zero]

/-- Zero second argument in the actual recursive polynomial. -/
theorem wordPolynomial_zero (w : List I) : wordPolynomial D w 0 = 0 := by
  induction w with
  | nil => simp [wordPolynomial]
  | cons i w ih => simp [wordPolynomial, ih]

/-- Different ROOT multidegrees vanish already in the actual polynomial;
no independence of their images in the weight group is used. -/
theorem wordPolynomial_grade (w : List I) {ν : I →₀ ℕ}
    {y : PreF Coefficients.Ring I} (hy : y ∈ weightSpace Coefficients.Ring ν)
    (hne : wordWeight w ≠ ν) : wordPolynomial D w y = 0 := by
  induction w generalizing ν y with
  | nil => simp [wordPolynomial, counit_eq_zero_of_mem (Ne.symm hne) hy]
  | cons i w ih =>
    by_cases hνi : ν i = 0
    · simp only [wordPolynomial, lDeriv_eq_zero D i hνi hy,
        rDeriv_eq_zero_of_mem _ i hνi hy, map_zero, wordPolynomial_zero,
        mul_zero, sub_zero]
    · have hν : ν = (ν - Finsupp.single i 1) + Finsupp.single i 1 := by
        ext j
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with hij
        · subst hij; omega
        · omega
      have htail : wordWeight w ≠ ν - Finsupp.single i 1 := by
        intro he
        apply hne
        rw [wordWeight_cons, he]
        exact (add_comm _ _).trans hν.symm
      have hy' : y ∈ weightSpace Coefficients.Ring
          ((ν - Finsupp.single i 1) + Finsupp.single i 1) := hν ▸ hy
      have hl := inverse_lDeriv_mem _ _ (chi_barChi D) i hy'
      have hr := rDeriv_mem_weightSpace (D.chi Coefficients.q pi) i hy'
      rw [wordPolynomial, weightTwist, parityTwist,
        ih (diagTwist_mem _ hl) htail,
        ih (diagTwist_mem _ hr) htail]
      simp

variable [DecidableEq X]

/-- Exact normalized positive-word Gram over the original modified algebra.
The polynomial is chosen independently of Λ, Μ and the coproduct choice. -/
theorem modifiedGram_pos_eq_eval (Λ Μ : X)
    (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (u v : List I) :
    modifiedGram D Λ Μ hΛ hΜ s
      (algebraWord D (Λ - Μ) (pos u)) (algebraWord D (Λ - Μ) (pos v)) =
    MvPolynomial.eval (deformationParameter D Μ) (normalizedReverse D u v) := by
  rw [modifiedGram_pos, normalizedReverse_eval_deformationParameter]
  by_cases huv : wordWeight u = wordWeight v
  · rw [map_mul, transported_scalar_cancellation D Λ Μ s u v huv]
  · rw [wordPolynomial_grade D u (monomial_mem_weightSpace v) huv]
    simp

/-- One fixed zero-constant residual polynomial for every positive pair. -/
theorem positive_residual_eq_eval (Λ Μ : X)
    (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (u v : List I) :
    modifiedGram D Λ Μ hΛ hΜ s
      (algebraWord D (Λ - Μ) (pos u)) (algebraWord D (Λ - Μ) (pos v)) -
      D.form Coefficients.q pi (monomial Coefficients.Ring u) (monomial Coefficients.Ring v) =
    MvPolynomial.eval (deformationParameter D Μ) (reciprocalError D u v) := by
  rw [modifiedGram_pos_eq_eval, reciprocalError, map_sub, MvPolynomial.eval_C]

/-- Quantifiers certify weight and coproduct independence, not a weight-dependent floor. -/
theorem fixed_positive_residual (u v : List I) :
    ∃ p : MvPolynomial I Coefficients.Ring,
      MvPolynomial.constantCoeff p = 0 ∧
      ∀ (Λ Μ : X) (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) (s : Bool),
        modifiedGram D Λ Μ hΛ hΜ s
          (algebraWord D (Λ - Μ) (pos u)) (algebraWord D (Λ - Μ) (pos v)) -
          D.form Coefficients.q pi (monomial Coefficients.Ring u) (monomial Coefficients.Ring v) =
        MvPolynomial.eval (deformationParameter D Μ) p :=
  ⟨reciprocalError D u v, reciprocalError_constantCoeff D u v,
    fun Λ Μ hΛ hΜ s ↦ positive_residual_eq_eval D Λ Μ hΛ hΜ s u v⟩

end OddMath.CoveringQuantum.UDot.PositiveComparison
