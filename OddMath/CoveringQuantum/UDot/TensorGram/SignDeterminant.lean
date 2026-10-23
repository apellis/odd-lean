/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.TensorGram.SignExpansion
import OddMath.CoveringQuantum.UDot.TensorGram.JointConvergence
import Mathlib.Topology.Instances.Matrix

/-!
# The Gram matrix of the form on `U̇` at `π = -1` on matched normal words

Let `W` be a finite set of words spanning the negative fiber of the half algebra at `π = -1`
with invertible specialized Gram matrix (`SignExpansion.exists_spans`). For a column `ζ` the
matched normal words `F_a 1_ζ E_b`, `a, b ∈ W`, have an invertible Gram matrix for the positive
modified form specialized at `π = -1`.

The proof compares, at dominant weights `Λ`, `Μ` with `Λ - Μ = ζ`, the transported tensor Gram
with the Gram matrix of the leading tensors: the expansion of a normal word in leading tensors is
triangular for the word lengths with unit diagonal (`SignExpansion.normalWord_expansion`), so
the two determinants agree. The leading Gram is a sign times fixed polynomials evaluated at the
deformation parameters of `Λ` and `Μ` (`MixedNormalized.leading_gram`), whose constant terms are
the half form. Along `(ζ + nξ, nξ)` the transported Gram converges to the positive modified form
and the leading Gram converges to a diagonal sign matrix times the Kronecker square of the Gram
matrix of `W`, which is invertible.

This is the main step of the nondegeneracy of the form on `U̇` at `π = -1` (Brundan–Ellis,
arXiv:1701.04133v2, Theorem 10.1) without the bar-consistency hypothesis (10.2). The argument
is ours.
-/

noncomputable section
open scoped Topology
open Filter Matrix
open scoped Kronecker
namespace OddMath.CoveringQuantum.UDot.SignDeterminant
open PreF Coefficients TensorProduct GenericVerma MixedGram PolarizationTransport
open BarDerivatives TensorPositive Reciprocal PositiveComparison
open NegativeComparison MixedNormalized SignSpanning SignExpansion NormalizedJointLimit
open NormalizedMixedComparison

/-- A matrix over a field which is triangular for a height function, with nonzero diagonal, has
determinant the product of its diagonal entries. -/
theorem det_eq_prod_diag {T F : Type*} [Fintype T] [DecidableEq T] [Field F] (M : Matrix T T F)
    (h : T → ℕ) (hd : ∀ i, M i i ≠ 0) (hlow : ∀ i j, i ≠ j → M i j ≠ 0 → h j < h i) :
    M.det = ∏ i, M i i := by
  have hM : M = diagonal (fun i ↦ M i i) * of (fun i j ↦ M i j / M i i) := by
    ext i j
    simp [diagonal_mul, mul_div_cancel₀ _ (hd i)]
  conv_lhs => rw [hM]
  rw [det_mul, det_diagonal, RowBasis.det_eq_one_of_triangular _ h, mul_one]
  · intro i
    simp [hd i]
  · intro i j hij hne
    exact hlow i j hij fun h0 ↦ hne (by simp [h0])

variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X)

/-- The matched normal word `F_a 1_ζ E_b` indexed by a pair of words of `W`. -/
abbrev pairWord {W : Finset (List I)} (ζ : X) (t : Pair W) : modified D Coefficients.q pi :=
  algebraWord D ζ (NegativeComparison.neg t.1.1 ++ pos t.2.1)

/-- The sign of the leading Gram on the row `t`. -/
def rowSign {W : Finset (List I)} (ζ : X) (t : Pair W) : RatFunc ℚ :=
  sgn (wordSign D (ζ + halfWeight D true (wordWeight t.2.1)) t.1.1)

/-- The specialized leading Gram at the weights `Λ`, `Μ`. -/
def leadingMatrix {W : Finset (List I)} (ζ Λ Μ : X) : Matrix (Pair W) (Pair W) (RatFunc ℚ) :=
  of fun t t' ↦
    if wordWeight t.1.1 = wordWeight t'.1.1 ∧ wordWeight t.2.1 = wordWeight t'.2.1 then
      rowSign D ζ t * sgn (MvPolynomial.eval (deformationParameter D Λ)
          (normalizedReverse D t.1.1 t'.1.1)) *
        sgn (MvPolynomial.eval (deformationParameter D Μ) (normalizedReverse D t.2.1 t'.2.1))
    else 0

/-- **Determinant comparison.** At dominant weights the transported tensor Gram of the matched
normal words and the leading Gram have the same determinant at `π = -1`. -/
theorem det_gram_eq {L : ℕ} {W : Finset (List I)} (hW : Spans D L W)
    (hWL : ∀ w ∈ W, w.length ≤ L) (ζ Λ Μ : X) (hζ : Λ - Μ = ζ)
    (hΛ : ∀ i, 0 ≤ D.h i Λ) (hΜ : ∀ i, 0 ≤ D.h i Μ) :
    (of fun t t' : Pair W ↦
      sgn (modifiedGram D Λ Μ hΛ hΜ true (pairWord D ζ t) (pairWord D ζ t'))).det =
      (leadingMatrix D ζ Λ Μ : Matrix (Pair W) (Pair W) _).det := by
  classical
  subst hζ
  choose P hPd hPl hP using fun t : Pair W ↦ normalWord_expansion D Λ Μ hW hWL true
    (wordScalar D true (Λ - Μ) (NegativeComparison.neg t.1.1 ++ pos t.2.1)) t
  choose Q hQd hQl hQ using fun t : Pair W ↦ normalWord_expansion D Λ Μ hW hWL false
    (wordScalar D false (Λ - Μ) (NegativeComparison.neg t.1.1 ++ pos t.2.1)) t
  let H : Matrix (Pair W) (Pair W) (RatFunc ℚ) := of fun w w' ↦
    sgn (tensorPolarization D Λ Μ hΛ hΜ (leadingTensor D Λ Μ w.1.1 w.2.1)
      (leadingTensor D Λ Μ w'.1.1 w'.2.1))
  have hG : (of fun t t' : Pair W ↦
      sgn (modifiedGram D Λ Μ hΛ hΜ true (pairWord D (Λ - Μ) t) (pairWord D (Λ - Μ) t'))) =
      (of P * H * (of Q)ᵀ).map ratBar := by
    ext t t'
    have hl := word_transport D true (Λ - Μ) (NegativeComparison.neg t.1.1 ++ pos t.2.1)
    have hr := word_transport D false (Λ - Μ) (NegativeComparison.neg t'.1.1 ++ pos t'.2.1)
    simp only [↓reduceIte, Bool.false_eq_true] at hl hr
    change sgn (gram D Λ Μ hΛ hΜ true (pairWord D (Λ - Μ) t).val
      (pairWord D (Λ - Μ) t').val) = _
    rw [gram_apply, hl, hr, algebraWord_normalWord, algebraWord_normalWord, map_smul,
      map_smul, LinearMap.smul_apply, LinearMap.smul_apply, sgn_bar, ← sgn_bilin, hP t,
      Bool.not_true, hQ t', Matrix.map_apply]
    congr 1
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smul, LinearMap.smul_apply,
      smul_eq_mul, map_mul, sgn_algebraMap, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply, Finset.sum_mul, sgn_negativeIdempotent, H]
    refine Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun w' _ ↦ ?_
    ring
  have hPdet : (of P).det = ∏ t, P t t := by
    refine det_eq_prod_diag _ height (fun t ↦ ?_) (fun t w htw hne ↦ ?_)
    · rw [of_apply, hPd t, map_mul]
      exact mul_ne_zero ((wordScalar_isUnit D _ _ _).map sgn).ne_zero
        ((NativeLeading.leadingScalar_isUnit D Λ Μ _ _ _).map sgn).ne_zero
    · have := hPl t w (Ne.symm htw) hne
      simp only [height]
      omega
  have hQdet : (of Q).det = ∏ t, Q t t := by
    refine det_eq_prod_diag _ height (fun t ↦ ?_) (fun t w htw hne ↦ ?_)
    · rw [of_apply, hQd t, map_mul]
      exact mul_ne_zero ((wordScalar_isUnit D _ _ _).map sgn).ne_zero
        ((NativeLeading.leadingScalar_isUnit D Λ Μ _ _ _).map sgn).ne_zero
    · have := hQl t w (Ne.symm htw) hne
      simp only [height]
      omega
  have hN : (leadingMatrix D (Λ - Μ) Λ Μ : Matrix (Pair W) (Pair W) _) =
      (diagonal (fun t ↦ P t t) * H * diagonal (fun t ↦ Q t t)).map ratBar := by
    ext t t'
    simp only [Matrix.map_apply, diagonal_mul, mul_diagonal, leadingMatrix, of_apply, H]
    split_ifs with hw
    · have e := congrArg sgn (leading_gram D Λ Μ hΛ hΜ true _ _ _ _ hw.1 hw.2)
      simp only [sgn_bar, map_mul, Bool.not_true] at e
      rw [rowSign, ← e, hPd, hQd]
      simp only [map_mul]
      ring
    · rw [leading_gram_eq_zero D Λ Μ hΛ hΜ _ _ _ _ hw]
      simp
  rw [hG, hN, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    ← RingHom.map_det, det_mul, det_mul, det_mul, det_mul, det_transpose, hPdet, hQdet,
    det_diagonal, det_diagonal]

/-- The limit of the leading Gram: a diagonal sign matrix times the Kronecker square of the
specialized Gram matrix of `W`. -/
def limitMatrix (W : Finset (List I)) (ζ : X) : Matrix (Pair W) (Pair W) (RatFunc ℚ) :=
  diagonal (rowSign D ζ) * kroneckerMap (· * ·) (wordGram D W) (wordGram D W)

omit [DecidableEq X] in
theorem det_limitMatrix_ne_zero {W : Finset (List I)} (hdet : (wordGram D W).det ≠ 0) (ζ : X) :
    (limitMatrix D W ζ).det ≠ 0 := by
  classical
  rw [limitMatrix, det_mul, det_diagonal]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun t _ ↦ ?_) ?_
  · intro h0
    have h := congrArg sgn
      (wordSign_sq D (ζ + halfWeight D true (wordWeight t.2.1)) t.1.1)
    rw [map_pow, map_one] at h
    rw [rowSign] at h0
    rw [h0] at h
    simp at h
  · change (wordGram D W ⊗ₖ wordGram D W).det ≠ 0
    rw [det_kronecker]
    exact mul_ne_zero (pow_ne_zero _ hdet) (pow_ne_zero _ hdet)

omit [DecidableEq X] in
/-- The normalized reciprocal polynomials converge to the half form at `π = -1` as the weight
goes to infinity. -/
theorem tendsto_sgn_normalizedReverse (a a' : List I) (f : ℕ → X)
    (hf : ∀ B : ℤ, ∀ᶠ n in atTop, ∀ i, B ≤ D.h i (f n)) :
    Tendsto (fun n ↦ sgn (MvPolynomial.eval (deformationParameter D (f n))
        (normalizedReverse D a a')))
      atTop (𝓝 (sgn (D.form Coefficients.q pi (monomial Coefficients.Ring a)
        (monomial Coefficients.Ring a')))) := by
  have h0 : Tendsto (fun n ↦ sgn (MvPolynomial.eval (deformationParameter D (f n))
      (reciprocalError D a a'))) atTop (𝓝 0) := by
    apply QAdic.tendsto_zero_of_order
    intro N
    filter_upwards [hf (threshold (reciprocalError D a a') (-1) (by norm_num) N)] with n hn
    exact polynomial_order D _ (reciprocalError_constantCoeff D a a') (-1) _ N (f n)
      fun i _ ↦ hn i
  have h1 := h0.add_const (sgn (D.form Coefficients.q pi (monomial Coefficients.Ring a)
    (monomial Coefficients.Ring a')))
  rw [zero_add] at h1
  refine h1.congr fun n ↦ ?_
  simp [reciprocalError]

/-- **Invertible Gram at `π = -1`.** For a finite spanning set `W` of words with invertible
specialized Gram matrix, the matched normal words `F_a 1_ζ E_b`, `a, b ∈ W`, have an invertible
Gram matrix for the positive modified form specialized at `π = -1`, provided some weight pairs
positively with every simple coroot. -/
theorem det_signGram_ne_zero [Finite I] {L : ℕ} {W : Finset (List I)} (hW : Spans D L W)
    (hWL : ∀ w ∈ W, w.length ≤ L) (hdet : (wordGram D W).det ≠ 0) (ζ ξ : X)
    (hξ : ∀ i, 0 < D.h i ξ) :
    (of fun t t' : Pair W ↦ sgn (GenericTensor.positiveModifiedForm D (pairWord D ζ t)
      (pairWord D ζ t'))).det ≠ 0 := by
  classical
  let G : ℕ → Matrix (Pair W) (Pair W) (RatFunc ℚ) := fun n ↦ of fun t t' ↦
    sgn (gramExtension D ζ (pairWord D ζ t) (pairWord D ζ t') true (cofinalPair ζ ξ n))
  have hG : Tendsto (fun n ↦ (G n).det) atTop (𝓝 (of fun t t' : Pair W ↦
      sgn (GenericTensor.positiveModifiedForm D (pairWord D ζ t) (pairWord D ζ t'))).det) :=
    ((continuous_id.matrix_det).tendsto _).comp (tendsto_pi_nhds.mpr fun t ↦
      tendsto_pi_nhds.mpr fun t' ↦ cofinalPair_gram_tendsto D ζ ξ hξ _ _
        (algebraWord_mul_one D ζ _) (algebraWord_mul_one D ζ _) (-1) (by norm_num) true)
  have hlower : ∀ B : ℤ, ∀ᶠ n : ℕ in atTop,
      (∀ i, B ≤ D.h i (ζ + n • ξ)) ∧ ∀ i, B ≤ D.h i (n • ξ) := fun B ↦
    (cofinalPair_tendsto D ζ ξ hξ).eventually (jointFilter_eventually_lower D ζ B)
  have hN : Tendsto (fun n : ℕ ↦
      (leadingMatrix D ζ (ζ + n • ξ) (n • ξ) : Matrix (Pair W) (Pair W) _).det)
      atTop (𝓝 (limitMatrix D W ζ).det) := by
    refine ((continuous_id.matrix_det).tendsto _).comp (tendsto_pi_nhds.mpr fun t ↦
      tendsto_pi_nhds.mpr fun t' ↦ ?_)
    simp only [diagonal_mul, kroneckerMap_apply, wordGram, of_apply]
    split_ifs with hw
    · rw [← mul_assoc]
      exact ((tendsto_sgn_normalizedReverse D _ _ _
        fun B ↦ (hlower B).mono fun _ h ↦ h.1).const_mul _).mul
        (tendsto_sgn_normalizedReverse D _ _ _ fun B ↦ (hlower B).mono fun _ h ↦ h.2)
    · have hz : sgn (D.form Coefficients.q pi (monomial Coefficients.Ring t.1.1)
            (monomial Coefficients.Ring t'.1.1)) *
          sgn (D.form Coefficients.q pi (monomial Coefficients.Ring t.2.1)
            (monomial Coefficients.Ring t'.2.1)) = 0 := by
        rcases not_and_or.mp hw with h | h
        · rw [PreF.form_eq_zero_of_ne _ _ h (monomial_mem_weightSpace _)
            (monomial_mem_weightSpace _), map_zero, zero_mul]
        · rw [PreF.form_eq_zero_of_ne _ _ h (monomial_mem_weightSpace _)
            (monomial_mem_weightSpace _), map_zero, mul_zero]
      rw [hz, mul_zero]
      exact tendsto_const_nhds
  have heq : ∀ᶠ n : ℕ in atTop, (G n).det =
      (leadingMatrix D ζ (ζ + n • ξ) (n • ξ) : Matrix (Pair W) (Pair W) _).det := by
    filter_upwards [cofinalPair_eventually_dominant D ζ ξ hξ] with n hn
    rw [← det_gram_eq D hW hWL ζ (ζ + n • ξ) (n • ξ) (add_sub_cancel_right _ _) hn.1 hn.2]
    congr 1
    ext t t'
    exact congrArg sgn (gramExtension_eq D ζ _ _ true (cofinalPair ζ ξ n) hn.1 hn.2)
  have : IsTopologicalRing (RatFunc ℚ) := Valued.isTopologicalDivisionRing.toIsTopologicalRing
  have : IsTopologicalAddGroup (RatFunc ℚ) := IsTopologicalRing.isTopologicalAddGroup
  have : T0Space (RatFunc ℚ) := ValuedRing.separated
  have : RegularSpace (RatFunc ℚ) := IsTopologicalAddGroup.regularSpace _
  have : T2Space (RatFunc ℚ) := inferInstance
  rw [tendsto_nhds_unique (hG.congr' heq) hN]
  exact det_limitMatrix_ne_zero D hdet ζ

end OddMath.CoveringQuantum.UDot.SignDeterminant
