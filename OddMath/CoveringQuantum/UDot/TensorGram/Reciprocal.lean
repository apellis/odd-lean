/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorGram.BarDerivatives

/-!
# Rectangular reversal of the finite comparison polynomial

Coefficient-bar reversal is defined over the covering ring, including its
zero divisors, with a root-multidegree support bound.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.Reciprocal
open PreF Coefficients GenericVerma BarDerivatives PolarizationTransport
open scoped BigOperators
variable {I X : Type*} [AddCommGroup X] [DecidableEq I]
variable (D : RootDatum I X)

/-- Rectangular, rather than merely total, degree bound for the actual polynomial. -/
theorem wordPolynomial_support (w : List I) (y : PreF Coefficients.Ring I)
    {m : I →₀ ℕ} (hm : m ∈ (wordPolynomial D w y).support) : m ≤ wordWeight w := by
  induction w generalizing y m with
  | nil =>
    have h := MvPolynomial.support_monomial_subset hm
    simpa [wordPolynomial, MvPolynomial.C] using h
  | cons i w ih =>
    rw [wordPolynomial, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
    have hs := MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hm)
    rcases Finset.mem_union.mp (MvPolynomial.support_sub I _ _ hs) with h | h
    · exact (ih _ h).trans (by rw [wordWeight_cons]; exact le_add_left le_rfl)
    · rw [MvPolynomial.support_X_mul, Finset.mem_map] at h
      obtain ⟨n, hn, rfl⟩ := h
      change Finsupp.single i 1 + n ≤ wordWeight (i :: w)
      rw [wordWeight_cons]
      exact add_le_add_right (ih _ hn) _

/-- Coefficient-bar rectangular reversal. No evaluation parameter enters its definition. -/
def reverse (a : I →₀ ℕ) (p : MvPolynomial I Coefficients.Ring) :
    MvPolynomial I Coefficients.Ring :=
  ∑ m ∈ p.support, MvPolynomial.monomial (a - m) (bar (p.coeff m))

omit [DecidableEq I] in
/-- Reversal stays in the same rectangle, including over a ring with zero divisors. -/
theorem reverse_support (a : I →₀ ℕ) (p : MvPolynomial I Coefficients.Ring)
    {n : I →₀ ℕ} (hn : n ∈ (reverse a p).support) : n ≤ a := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hn)
  have he := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
  exact he ▸ tsub_le_self

omit [DecidableEq I] in
/-- Under the rectangle bound, the reversed constant is exactly the barred top coefficient. -/
theorem reverse_constantCoeff (a : I →₀ ℕ) (p : MvPolynomial I Coefficients.Ring)
    (hp : ∀ m ∈ p.support, m ≤ a) :
    MvPolynomial.constantCoeff (reverse a p) = bar (p.coeff a) := by
  classical
  simp only [reverse, map_sum, MvPolynomial.constantCoeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro m hm hma
    have hne : a - m ≠ 0 := by
      intro he
      exact hma (le_antisymm (hp m hm) (tsub_eq_zero_iff_le.mp he))
    simp [hne]
  · intro ha
    simp [MvPolynomial.notMem_support_iff.mp ha]

omit [DecidableEq I] in
/-- Every coefficient is fixed by reversal of the rectangle, not by interpolation. -/
theorem reverse_coeff (a : I →₀ ℕ) (p : MvPolynomial I Coefficients.Ring)
    (hp : ∀ m ∈ p.support, m ≤ a) {n : I →₀ ℕ} (hn : n ≤ a) :
    (reverse a p).coeff n = bar (p.coeff (a - n)) := by
  classical
  rw [reverse, MvPolynomial.coeff_sum, Finset.sum_eq_single (a - n)]
  · simp [tsub_tsub_cancel_of_le hn]
  · intro m hm hmn
    have hne : a - m ≠ n := by
      intro he
      apply hmn
      rw [← he, tsub_tsub_cancel_of_le (hp m hm)]
    simp [hne]
  · intro ha
    simp [MvPolynomial.notMem_support_iff.mp ha]

/-- Evaluation of a pure monomial, without its coefficient. -/
def monomialValue (t : I → Coefficients.Ring) (a : I →₀ ℕ) : Coefficients.Ring :=
  a.prod fun i n ↦ t i ^ n

omit [DecidableEq I] in
private theorem monomialValue_add (t : I → Coefficients.Ring) (a b : I →₀ ℕ) :
    monomialValue t (a + b) = monomialValue t a * monomialValue t b := by
  exact Finsupp.prod_add_index' (by simp) (by intros; exact pow_add _ _ _)

omit [DecidableEq I] in
private theorem monomialValue_bar (t : I → Coefficients.Ring)
    (ht : ∀ i, t i * bar (t i) = 1) (a : I →₀ ℕ) :
    monomialValue t a * bar (monomialValue t a) = 1 := by
  simp only [monomialValue, Finsupp.prod, map_prod, map_pow,
    ← Finset.prod_mul_distrib, ← mul_pow, ht, one_pow, Finset.prod_const_one]

omit [DecidableEq I] in
private theorem monomialValue_sub (t : I → Coefficients.Ring)
    (ht : ∀ i, t i * bar (t i) = 1) {a m : I →₀ ℕ} (hm : m ≤ a) :
    monomialValue t (a - m) = monomialValue t a * bar (monomialValue t m) := by
  conv_rhs => rw [← tsub_add_cancel_of_le hm, monomialValue_add]
  rw [mul_assoc, monomialValue_bar t ht, mul_one]

omit [DecidableEq I] in
/-- Actual evaluation identity; `ht` says the bar is the inverse of each parameter. -/
theorem reverse_eval (a : I →₀ ℕ) (p : MvPolynomial I Coefficients.Ring)
    (hp : ∀ m ∈ p.support, m ≤ a) (t : I → Coefficients.Ring)
    (ht : ∀ i, t i * bar (t i) = 1) :
    MvPolynomial.eval t (reverse a p) =
      monomialValue t a * bar (MvPolynomial.eval t p) := by
  classical
  conv_rhs => rw [p.as_sum]
  simp only [reverse, map_sum, MvPolynomial.eval_monomial, map_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  change bar (p.coeff m) * monomialValue t (a - m) =
    monomialValue t a * (bar (p.coeff m) * bar (monomialValue t m))
  rw [monomialValue_sub t ht (hp m hm)]
  ring

/-- Fixed normalized reciprocal of the actual word comparison polynomial.
Both words may have arbitrary, unrelated root multidegrees. -/
def normalizedReverse (w v : List I) : MvPolynomial I Coefficients.Ring :=
  MvPolynomial.C (bar (topScale D w)) *
    reverse (wordWeight w) (wordPolynomial D w (monomial Coefficients.Ring v))

/-- Normalized reciprocal support is contained in the full first-word rectangle. -/
theorem normalizedReverse_support (w v : List I) {m : I →₀ ℕ}
    (hm : m ∈ (normalizedReverse D w v).support) : m ≤ wordWeight w := by
  rw [normalizedReverse, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
  exact reverse_support _ _ (MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hm))

/-- All coefficients are explicit, with no highest-weight dependence. -/
theorem normalizedReverse_coeff (w v : List I) {n : I →₀ ℕ} (hn : n ≤ wordWeight w) :
    (normalizedReverse D w v).coeff n = bar (topScale D w) *
      bar ((wordPolynomial D w (monomial Coefficients.Ring v)).coeff (wordWeight w - n)) := by
  rw [normalizedReverse, MvPolynomial.coeff_C_mul,
    reverse_coeff _ _ (fun _ hm ↦ wordPolynomial_support D w _ hm) hn]

/-- The constant is the original half form, not a replacement pairing. -/
theorem normalizedReverse_constantCoeff (w v : List I) :
    MvPolynomial.constantCoeff (normalizedReverse D w v) =
      D.form Coefficients.q pi (monomial Coefficients.Ring w) (monomial Coefficients.Ring v) := by
  rw [normalizedReverse, map_mul, MvPolynomial.constantCoeff_C,
    reverse_constantCoeff _ _ (fun _ hm ↦ wordPolynomial_support D w _ hm)]
  exact normalized_bar_coeff_wordPolynomial D w v

/-- The fixed polynomial evaluates to the normalized barred actual polynomial. -/
theorem normalizedReverse_eval (w v : List I) (t : I → Coefficients.Ring)
    (ht : ∀ i, t i * bar (t i) = 1) :
    MvPolynomial.eval t (normalizedReverse D w v) =
      bar (topScale D w) * monomialValue t (wordWeight w) *
        bar (MvPolynomial.eval t (wordPolynomial D w (monomial Coefficients.Ring v))) := by
  rw [normalizedReverse, map_mul, MvPolynomial.eval_C,
    reverse_eval _ _ (fun _ hm ↦ wordPolynomial_support D w _ hm) t ht, mul_assoc]

omit [DecidableEq I] in
/-- The actual highest-weight deformation parameters have bar as their inverse. -/
theorem deformationParameter_mul_bar (Λ : X) (i : I) :
    deformationParameter D Λ i * bar (deformationParameter D Λ i) = 1 := by
  simp only [deformationParameter, map_mul, map_pow, barData.map_pii, qi_zpow,
    barData.map_qp]
  have hp : (D.pii pi i ^ (D.h i Λ).natAbs) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm _ 2, pow_mul, D.pii_sq pi pi_sq, one_pow]
  calc
    _ = (D.pii pi i ^ (D.h i Λ).natAbs) ^ 2 *
        (qp Coefficients.q (D.d i * (2 * D.h i Λ)) *
          qp Coefficients.q (-(D.d i * (2 * D.h i Λ)))) := by ring
    _ = 1 := by rw [hp, qp_mul, add_neg_cancel, qp_zero, one_mul]

/-- Evaluation at the actual deformation parameters, with no assumed inverse law. -/
theorem normalizedReverse_eval_deformationParameter (w v : List I) (Λ : X) :
    MvPolynomial.eval (deformationParameter D Λ) (normalizedReverse D w v) =
      bar (topScale D w) * monomialValue (deformationParameter D Λ) (wordWeight w) *
        bar (MvPolynomial.eval (deformationParameter D Λ)
          (wordPolynomial D w (monomial Coefficients.Ring v))) :=
  normalizedReverse_eval D w v _ (deformationParameter_mul_bar D Λ)

/-- The fixed residual, independent of all highest weights. -/
def reciprocalError (w v : List I) : MvPolynomial I Coefficients.Ring :=
  normalizedReverse D w v - MvPolynomial.C
    (D.form Coefficients.q pi (monomial Coefficients.Ring w) (monomial Coefficients.Ring v))

/-- Exact zero residual constant. -/
theorem reciprocalError_constantCoeff (w v : List I) :
    MvPolynomial.constantCoeff (reciprocalError D w v) = 0 := by
  simp [reciprocalError, normalizedReverse_constantCoeff]

/-- The actual normalized barred evaluation differs from the half form by
one fixed polynomial with zero constant coefficient. -/
theorem reciprocalError_eval (w v : List I) (t : I → Coefficients.Ring)
    (ht : ∀ i, t i * bar (t i) = 1) :
    MvPolynomial.eval t (reciprocalError D w v) =
      bar (topScale D w) * monomialValue t (wordWeight w) *
        bar (MvPolynomial.eval t (wordPolynomial D w (monomial Coefficients.Ring v))) -
      D.form Coefficients.q pi (monomial Coefficients.Ring w) (monomial Coefficients.Ring v) := by
  rw [reciprocalError, map_sub, MvPolynomial.eval_C, normalizedReverse_eval D w v t ht]

end OddMath.CoveringQuantum.UDot.Reciprocal
