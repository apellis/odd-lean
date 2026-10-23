/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorGram.PositiveComparison
import OddMath.CoveringQuantum.UDot.NativeCyclic.MixedLeading

/-!
# Negative-word normalized tensor Gram comparison

The mirror image of `PositiveComparison`. On words in the generators `F_i` alone, the transported
tensor Gram of the column `Λ - Μ` is, up to a sign depending only on the column and the word,
one polynomial evaluated at the deformation parameters of the HIGHEST weight `Λ`. The polynomial
is independent of `Λ`, `Μ` and the coproduct choice, and its constant coefficient is the half
form. Together with the positive comparison this gives the two diagonal factors of the
finite-piece Gram determinant used for nondegeneracy at `π = -1` (BE2 Thm 10.1, without the
bar-consistency hypothesis (10.2)). The argument is ours.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.NegativeComparison
open PreF Coefficients TensorProduct GenericVerma MixedGram PolarizationTransport
open BarDerivatives TensorPositive Reciprocal ToralCancellation PositiveComparison
variable {I X : Type*} [AddCommGroup X] [DecidableEq I]
variable (D : RootDatum I X)

/-- All letters are the original negative generators. -/
def neg (w : List I) : List (Bool × I) := w.map (fun i ↦ (false, i))

omit [DecidableEq I] in
/-- Negative word shifts are the negatives of the root multidegree. -/
theorem shift_neg (w : List I) :
    shift D (neg w) = -halfWeight D true (wordWeight w) := by
  induction w with
  | nil => simp [neg, shift]
  | cons i w ih =>
    simp only [neg, List.map_cons, shift, wordWeight_cons, halfWeight_add,
      halfWeight_single, halfRoot] at *
    rw [ih]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    abel

omit [DecidableEq I] in
/-- A negative root word does not change the weight-block parity. -/
theorem parl_sub_word (i : I) (ζ : X) (w : List I) :
    D.parl i (ζ - halfWeight D true (wordWeight w)) = D.parl i ζ := by
  have h := parl_add_word D i (ζ - halfWeight D true (wordWeight w)) w
  rw [sub_add_cancel] at h
  exact h.symm

omit [DecidableEq I] in
/-- The negative transport factor changes by the symmetric root bicharacter. -/
theorem genScalar_sub_root (side : Bool) (i j : I) (ζ : X) :
    genScalar D side false i (ζ + -D.α j) =
      qp Coefficients.q (D.dot i j) * genScalar D side false i ζ := by
  have hp : D.parl i (ζ + -D.α j) = D.parl i ζ := by
    have h := D.parl_add_α i j (ζ + -D.α j)
    rw [neg_add_cancel_right] at h
    exact h.symm
  simp only [genScalar, Bool.false_eq_true, ite_false, hp, map_add, map_neg, D.h_α]
  rw [show -(D.d i * (D.h i ζ + -D.a i j - 1)) =
    D.dot i j + -(D.d i * (D.h i ζ - 1)) by simp only [SuperCartanDatum.dot]; ring]
  rw [← qp_mul]
  ring

omit [DecidableEq I] in
/-- Transport scalar invariance under permutations of a negative word. -/
theorem wordScalar_neg_perm (side : Bool) (ζ : X) {u v : List I} (h : u.Perm v) :
    wordScalar D side ζ (neg u) = wordScalar D side ζ (neg v) := by
  induction h with
  | nil => rfl
  | @cons i u v h ih =>
    simp only [neg, List.map_cons, wordScalar] at *
    rw [ih]
    congr 2
    exact congrArg (ζ + ·) ((shift_neg D u).trans
      ((congrArg (fun x ↦ -halfWeight D true x) (wordWeight_perm h)).trans
        (shift_neg D v).symm))
  | swap i j w =>
    simp only [neg, List.map_cons, wordScalar, shift, halfRoot, Bool.false_eq_true, ite_false]
    rw [← add_assoc, add_right_comm ζ (-D.α i), ← add_assoc,
      add_right_comm ζ (-D.α j)]
    rw [genScalar_sub_root, genScalar_sub_root, D.dot_comm i j]
    ring
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

variable [DecidableEq X] (Λ Μ : X)

/-- Exact all-negative collapse for either original coproduct: no lowering branch survives
when the second factor is the lowest vector. -/
theorem wordAction_neg (s : Bool) (a : List I) :
    wordAction D Λ Μ s (neg a) (vac D Λ Μ) =
      amplitude D false Μ a •
        (project D Λ (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
          toIntegrable D Μ 1) := by
  obtain ⟨r, hr, he⟩ := NativeLeading.negative_leading D Λ Μ s a []
  have hz : r = 0 := by
    simpa only [List.length_nil, NativeLeading.lowerBidegree_zero_right,
      Submodule.mem_bot] using hr
  have hw : wordAction D Λ Μ s (neg a) = NativeLeading.halfOperators D Λ Μ s false a := by
    simp only [wordAction, NativeLeading.halfOperators, neg, List.map_map, Function.comp_def]
  rw [hw]
  simpa only [hz, add_zero, project, monomial_nil, map_one, wordWeight_nil, halfWeight_zero,
    sub_zero] using he

/-- The highest form on words is the normalized polarization of a word. -/
theorem highest_word (hΛ : ∀ i, 0 ≤ D.h i Λ) (a : List I) (y : PreF Coefficients.Ring I) :
    integrablePolarization D Λ hΛ (project D Λ (monomial Coefficients.Ring a)) (project D Λ y) =
      wordSign D Λ a *
        MvPolynomial.eval (deformationParameter D Λ) (wordPolynomial D a y) := by
  rw [highest_polynomial, halfPolynomial_eval, normalizedPolarization, sign_involution]
  exact polarization_word_polynomial D Λ a y

/-- The lowest form of the lowest vector is one. -/
theorem lowest_one (hΜ : ∀ i, 0 ≤ D.h i Μ) :
    lowestPolarization D Μ hΜ (toIntegrable D Μ 1) (toIntegrable D Μ 1) = 1 := by
  have h := lowest_word D Μ hΜ [] []
  simp only [project, monomial_nil, map_one] at h
  rw [h]
  simp [wordPolynomial]

/-- Actual tensor Gram of two negative words, before coefficient-bar transport. -/
theorem tensor_gram_neg (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s t : Bool) (u v : List I) :
    tensorPolarization D Λ Μ hΛ hΜ
      (wordAction D Λ Μ s (neg u) (vac D Λ Μ))
      (wordAction D Λ Μ t (neg v) (vac D Λ Μ)) =
      amplitude D false Μ u * amplitude D false Μ v * wordSign D Λ u *
        MvPolynomial.eval (deformationParameter D Λ)
          (wordPolynomial D u (monomial Coefficients.Ring v)) := by
  rw [wordAction_neg, wordAction_neg, LinearMap.map_smul₂, LinearMap.map_smul,
    tensorPolarization_tmul, highest_word, lowest_one]
  simp only [smul_eq_mul, mul_one, mul_assoc]

/-- Exact transported Gram of two negative words on the original modified algebra. -/
theorem modifiedGram_neg (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (u v : List I) :
    modifiedGram D Λ Μ hΛ hΜ s
      (algebraWord D (Λ - Μ) (neg u)) (algebraWord D (Λ - Μ) (neg v)) =
      bar (wordScalar D true (Λ - Μ) (neg u) *
        wordScalar D false (Λ - Μ) (neg v) *
        amplitude D false Μ u * amplitude D false Μ v * wordSign D Λ u *
        MvPolynomial.eval (deformationParameter D Λ)
          (wordPolynomial D u (monomial Coefficients.Ring v))) := by
  change gram D Λ Μ hΛ hΜ s (algebraWord D (Λ - Μ) (neg u)).val
    (algebraWord D (Λ - Μ) (neg v)).val = _
  rw [gram_apply]
  have hl := word_transport D true (Λ - Μ) (neg u)
  have hr := word_transport D false (Λ - Μ) (neg v)
  simp only [ite_true, Bool.false_eq_true, ite_false] at hl hr
  rw [hl, hr]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, algebraWord_action,
    tensor_gram_neg, mul_assoc, mul_left_comm]

omit [DecidableEq I] [DecidableEq X] in
/-- Exact one-letter cancellation for a negative letter: the column sign, the leading
normalization and the barred highest-weight parameter. -/
theorem scalar_step_neg (i : I) (w : List I) :
    genScalar D true false i (Λ - Μ + shift D (neg w)) *
      genScalar D false false i (Λ - Μ + shift D (neg w)) *
      tensorToralScalar D false i Μ * tensorToralScalar D false i Μ *
      polarizationSign D Λ i =
    polarizationSign D (Λ - Μ) i *
      (D.pii pi i * qp Coefficients.q (2 * D.d i) *
        qp Coefficients.q (2 * D.d i * D.h i (halfWeight D true (wordWeight w)))) *
      bar (deformationParameter D Λ i) := by
  have hp : polarizationSign D Λ i = D.pii pi i * D.pii pi i ^ (D.h i Λ).natAbs := rfl
  have hs : D.pii pi i ^ 2 = 1 := D.pii_sq pi pi_sq i
  rw [shift_neg, ← sub_eq_add_neg]
  simp only [genScalar, ite_true, Bool.false_eq_true, ite_false, one_mul, parl_sub_word]
  rw [← polarizationSign_eq_parl]
  simp only [tensorToralScalar, Bool.false_eq_true, ite_false, one_mul, deformationParameter,
    map_mul, map_pow, barData.map_pii, qi_zpow, barData.map_qp, map_sub]
  rw [hp]
  calc
    _ = polarizationSign D (Λ - Μ) i * (D.pii pi i * D.pii pi i ^ (D.h i Λ).natAbs) *
        (qp Coefficients.q (-(D.d i * (D.h i Λ - D.h i Μ -
          D.h i (halfWeight D true (wordWeight w)) - 1))) *
         qp Coefficients.q (-(D.d i * (D.h i Λ - D.h i Μ -
          D.h i (halfWeight D true (wordWeight w)) - 1))) *
         qp Coefficients.q (-(D.d i * D.h i Μ)) *
         qp Coefficients.q (-(D.d i * D.h i Μ))) := by ring
    _ = _ := by
      simp only [qp_mul]
      rw [show -(D.d i * (D.h i Λ - D.h i Μ -
          D.h i (halfWeight D true (wordWeight w)) - 1)) +
          -(D.d i * (D.h i Λ - D.h i Μ -
          D.h i (halfWeight D true (wordWeight w)) - 1)) +
          -(D.d i * D.h i Μ) + -(D.d i * D.h i Μ) =
          2 * D.d i + 2 * D.d i * D.h i (halfWeight D true (wordWeight w)) +
          -(D.d i * (2 * D.h i Λ)) by ring]
      simp only [← qp_mul]
      ring

omit [DecidableEq I] [DecidableEq X] in
/-- All-word diagonal cancellation for negative words. -/
theorem scalar_diagonal_neg (w : List I) :
    wordScalar D true (Λ - Μ) (neg w) * wordScalar D false (Λ - Μ) (neg w) *
      amplitude D false Μ w * amplitude D false Μ w * wordSign D Λ w =
    wordSign D (Λ - Μ) w * topScale D w *
      bar (monomialValue (deformationParameter D Λ) (wordWeight w)) := by
  induction w with
  | nil => simp [neg, wordScalar, amplitude, topScale, monomialValue, wordSign]
  | cons i w ih =>
    change (genScalar D true false i (Λ - Μ + shift D (neg w)) *
        wordScalar D true (Λ - Μ) (neg w)) *
      (genScalar D false false i (Λ - Μ + shift D (neg w)) *
        wordScalar D false (Λ - Μ) (neg w)) *
      (tensorToralScalar D false i Μ * amplitude D false Μ w) *
      (tensorToralScalar D false i Μ * amplitude D false Μ w) *
      (polarizationSign D Λ i * wordSign D Λ w) = _
    calc
      _ = (genScalar D true false i (Λ - Μ + shift D (neg w)) *
          genScalar D false false i (Λ - Μ + shift D (neg w)) *
          tensorToralScalar D false i Μ * tensorToralScalar D false i Μ *
          polarizationSign D Λ i) *
        (wordScalar D true (Λ - Μ) (neg w) * wordScalar D false (Λ - Μ) (neg w) *
          amplitude D false Μ w * amplitude D false Μ w * wordSign D Λ w) := by ring
      _ = _ := by
        rw [scalar_step_neg, ih, topScale, monomialValue_cons, map_mul]
        simp only [wordSign, List.map_cons, List.prod_cons]
        ring

omit [DecidableEq I] [DecidableEq X] in
/-- Negative scalar cancellation for two words of equal root multidegree. -/
theorem scalar_cancellation_neg (u v : List I) (huv : wordWeight u = wordWeight v) :
    wordScalar D true (Λ - Μ) (neg u) * wordScalar D false (Λ - Μ) (neg v) *
      amplitude D false Μ u * amplitude D false Μ v * wordSign D Λ u =
    wordSign D (Λ - Μ) u * topScale D u *
      bar (monomialValue (deformationParameter D Λ) (wordWeight u)) := by
  have hp := perm_of_wordWeight_eq huv
  rw [← wordScalar_neg_perm D false (Λ - Μ) hp, ← amplitude_perm D false Μ hp]
  exact scalar_diagonal_neg D Λ Μ u

omit [DecidableEq I] [DecidableEq X] in
/-- The column sign is fixed by the coefficient bar. -/
theorem bar_wordSign (ζ : X) (w : List I) : bar (wordSign D ζ w) = wordSign D ζ w := by
  induction w with
  | nil => simp [wordSign]
  | cons i w ih =>
    simp only [wordSign, List.map_cons, List.prod_cons, map_mul] at *
    rw [ih]
    simp [polarizationSign, barData.map_pii]

/-- Exact normalized negative-word Gram over the original modified algebra: a sign depending
only on the column and the word, times one polynomial (independent of `Λ`, `Μ` and the
coproduct choice) evaluated at the highest weight's deformation parameters. -/
theorem modifiedGram_neg_eq_eval (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (u v : List I) :
    modifiedGram D Λ Μ hΛ hΜ s
      (algebraWord D (Λ - Μ) (neg u)) (algebraWord D (Λ - Μ) (neg v)) =
    wordSign D (Λ - Μ) u *
      MvPolynomial.eval (deformationParameter D Λ) (normalizedReverse D u v) := by
  rw [modifiedGram_neg, normalizedReverse_eval_deformationParameter]
  by_cases huv : wordWeight u = wordWeight v
  · rw [map_mul, scalar_cancellation_neg D Λ Μ u v huv, map_mul, map_mul, bar_bar,
      bar_wordSign]
    ring
  · rw [wordPolynomial_grade D u (monomial_mem_weightSpace v) huv]
    simp

/-- One fixed zero-constant residual polynomial for every negative pair. -/
theorem negative_residual_eq_eval (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (s : Bool) (u v : List I) :
    wordSign D (Λ - Μ) u * modifiedGram D Λ Μ hΛ hΜ s
      (algebraWord D (Λ - Μ) (neg u)) (algebraWord D (Λ - Μ) (neg v)) -
      D.form Coefficients.q pi (monomial Coefficients.Ring u) (monomial Coefficients.Ring v) =
    MvPolynomial.eval (deformationParameter D Λ) (reciprocalError D u v) := by
  rw [modifiedGram_neg_eq_eval, reciprocalError, map_sub, MvPolynomial.eval_C, ← mul_assoc]
  have h := wordSign_sq D (Λ - Μ) u
  rw [pow_two] at h
  rw [h, one_mul]

end OddMath.CoveringQuantum.UDot.NegativeComparison
