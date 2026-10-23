/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorGram.NegativeComparison
import OddMath.CoveringQuantum.UDot.TensorGram.MixedIntegration

/-!
# Leading terms of the normalized tensor Gram on matched normal words

A matched normal word `F_a 1 E_b` of the modified algebra acts on the tensor of a highest and a
lowest vector by a unit times `F_a v_Λ ⊗ E_b v_Μ`, up to tensors of strictly shorter words
(`GenericVerma.NativeLeading.normalWord_leading`). Here we compute the transported tensor Gram
of these leading tensors exactly: up to a sign depending only on the column and the negative
word, it is the product of two fixed polynomials (independent of `Λ`, `Μ` and the coproduct
choice), the first evaluated at the deformation parameters of `Λ` and the second at those of
`Μ`. Their constant coefficients are the half form on the negative words and on the positive
words. This is the diagonal input of the Gram determinant used for nondegeneracy of the form on
`U̇` at `π = -1` (Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.1) without the bar-consistency
hypothesis (10.2). The argument is ours.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.MixedNormalized
open PreF Coefficients TensorProduct GenericVerma MixedGram PolarizationTransport
open BarDerivatives TensorPositive Reciprocal ToralCancellation PositiveComparison
open NegativeComparison NormalizedMixedComparison
variable {I X : Type*} [AddCommGroup X] [DecidableEq I]
variable (D : RootDatum I X)

omit [DecidableEq I] in
theorem halfWeight_false (ν : I →₀ ℕ) : halfWeight D false ν = -halfWeight D true ν := by
  simp [halfWeight, halfRoot, Finsupp.sum, Finset.sum_neg_distrib]

omit [DecidableEq I] in
theorem shift_append (a b : List (Bool × I)) : shift D (a ++ b) = shift D a + shift D b := by
  induction a with
  | nil => simp [shift]
  | cons g a ih => simp only [List.cons_append, shift, ih, add_assoc]

omit [DecidableEq I] in
/-- Transport scalars of a concatenated word factor through the intermediate weight. -/
theorem wordScalar_append (side : Bool) (ζ : X) (a b : List (Bool × I)) :
    wordScalar D side ζ (a ++ b) = wordScalar D side (ζ + shift D b) a * wordScalar D side ζ b := by
  induction a with
  | nil => simp [wordScalar]
  | cons g a ih =>
    simp only [List.cons_append, wordScalar, ih, shift_append, mul_assoc]
    rw [show ζ + (shift D a + shift D b) = ζ + shift D b + shift D a by abel]

omit [DecidableEq I] in
/-- Transport scalars are units. -/
theorem wordScalar_isUnit (side : Bool) (ζ : X) (w : List (Bool × I)) :
    IsUnit (wordScalar D side ζ w) := by
  have hpi : IsUnit (pi : Coefficients.Ring) :=
    isUnit_iff_exists_inv.mpr ⟨pi, by simpa only [pow_two] using pi_sq⟩
  induction w with
  | nil => exact isUnit_one
  | cons g w ih =>
    refine IsUnit.mul ?_ ih
    unfold genScalar qp
    split_ifs
    all_goals first
      | exact isUnit_one.mul (Units.isUnit _)
      | exact (hpi.pow _).mul (Units.isUnit _)

variable [DecidableEq X]

/-- The algebra word of a negative word followed by a positive word is the matched normal
word. -/
theorem algebraWord_normalWord (ζ : X) (a b : List I) :
    (algebraWord D ζ (neg a ++ pos b)).val = normalWord D Coefficients.q pi a b ζ := by
  induction a with
  | nil =>
    have h := congrArg Subtype.val (algebraWord_pos_eq D ζ b)
    simp only [NegativeComparison.neg, List.map_nil, List.nil_append] at h ⊢
    rw [h, normalWord, word]
    exact (halfWord_mem_block D Coefficients.q pi true b ζ).1.symm
  | cons i a ih =>
    change halfGen D Coefficients.q pi false i (ζ + shift D (neg a ++ pos b)) *
      (algebraWord D ζ (neg a ++ pos b)).val = _
    rw [ih, normalWord, normalWord, halfWord, mul_assoc, shift_append, shift_neg, shift_pos,
      halfWeight_false]
    congr 2
    abel

variable (Λ Μ : X)

/-- The leading tensor of a matched normal word. -/
abbrev leadingTensor (a b : List I) :
    IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ :=
  project D Λ (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
    project D Μ (monomial Coefficients.Ring b)

/-- **Normalized leading Gram.** For words of equal root multidegrees, the transported tensor
Gram of the leading tensors of two matched normal words, normalized by their transport and
leading scalars, is a sign depending only on the column and the negative word, times the fixed
normalized reciprocal polynomials of the negative words at `Λ` and of the positive words
at `Μ`. -/
theorem leading_gram (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) (s : Bool)
    (a b a' b' : List I) (ha : wordWeight a = wordWeight a') (hb : wordWeight b = wordWeight b') :
    bar (wordScalar D true (Λ - Μ) (neg a ++ pos b) *
        wordScalar D false (Λ - Μ) (neg a' ++ pos b') *
        NativeLeading.leadingScalar D Λ Μ s a b * NativeLeading.leadingScalar D Λ Μ (!s) a' b' *
        tensorPolarization D Λ Μ hΛ hΜ (leadingTensor D Λ Μ a b) (leadingTensor D Λ Μ a' b')) =
      wordSign D (Λ - Μ + halfWeight D true (wordWeight b)) a *
        MvPolynomial.eval (deformationParameter D Λ) (normalizedReverse D a a') *
        MvPolynomial.eval (deformationParameter D Μ) (normalizedReverse D b b') := by
  rw [leadingTensor, leadingTensor, tensorPolarization_tmul, highest_word D Λ hΛ a,
    lowest_word D Μ hΜ b b', wordScalar_append, wordScalar_append, shift_pos, shift_pos,
    NativeLeading.leadingScalar, NativeLeading.leadingScalar, ← hb,
    normalizedReverse_eval_deformationParameter, normalizedReverse_eval_deformationParameter]
  have hζ : Λ - Μ + halfWeight D true (wordWeight b) =
      Λ - (Μ - halfWeight D true (wordWeight b)) := by abel
  rw [hζ]
  set Μ' := Μ - halfWeight D true (wordWeight b)
  have hn := scalar_cancellation_neg D Λ Μ' a a' ha
  have hp := transported_scalar_cancellation D Λ Μ s b b' hb
  calc _ = bar ((wordScalar D true (Λ - Μ') (neg a) * wordScalar D false (Λ - Μ') (neg a') *
          amplitude D false Μ' a * amplitude D false Μ' a' * wordSign D Λ a) *
        (wordScalar D true (Λ - Μ) (pos b) * wordScalar D false (Λ - Μ) (pos b') *
          amplitude D s Λ b * amplitude D (!s) Λ b') *
        MvPolynomial.eval (deformationParameter D Λ)
          (wordPolynomial D a (monomial Coefficients.Ring a')) *
        MvPolynomial.eval (deformationParameter D Μ)
          (wordPolynomial D b (monomial Coefficients.Ring b'))) := by
        congr 1
        ring
    _ = _ := by
        rw [map_mul, map_mul, map_mul, hn, hp, map_mul, map_mul, bar_bar, bar_wordSign]
        ring

/-- Leading tensors of different bidegrees are orthogonal. -/
theorem leading_gram_eq_zero (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ)
    (a b a' b' : List I) (h : ¬(wordWeight a = wordWeight a' ∧ wordWeight b = wordWeight b')) :
    tensorPolarization D Λ Μ hΛ hΜ (leadingTensor D Λ Μ a b) (leadingTensor D Λ Μ a' b') = 0 := by
  rw [leadingTensor, leadingTensor, tensorPolarization_tmul, highest_word D Λ hΛ a,
    lowest_word D Μ hΜ b b']
  by_cases ha : wordWeight a = wordWeight a'
  · rw [wordPolynomial_grade D b (monomial_mem_weightSpace b') (fun hb ↦ h ⟨ha, hb⟩)]
    simp
  · rw [wordPolynomial_grade D a (monomial_mem_weightSpace a') ha]
    simp

end OddMath.CoveringQuantum.UDot.MixedNormalized
