import OddMath.Frontier.EKAntipode

/-! Postproduction controls on the actual maps. Preproduction conditional
contractions and composition controls are preserved in an unpublished script -/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators TensorProduct
namespace OddMath.Frontier.EKAntipodeControls
open EKRadicalQuotient (Q quotientCounit)
open EKElementaryQuotient (h e)
open EKAutomorphisms EKAntipode
open EKCoideal (quotientCoproduct)
open EKSignedQuotient (quotientTensorMul)

private theorem h_degree (n : ℕ) : h n ∈ EKIntegralBases.degreePiece n := by
  simpa using hWord_degree [n]
private theorem tensor_h (a b c d : ℕ) :
    quotientTensorMul (h a ⊗ₜ[ℤ] h b) (h c ⊗ₜ[ℤ] h d) =
      (-1 : ℤ)^(b*c) • ((h a*h c) ⊗ₜ[ℤ] (h b*h d)) :=
  tensorMul_homogeneous (h_degree a) (h_degree b) (h_degree c) (h_degree d)
private theorem h_zero : h 0 = 1 := by simp [h]

/-- Direct small generator checks, not calls to the general convolution proof. -/
theorem unit_both : leftContraction (quotientCoproduct (1 : Q)) = 1 ∧
    rightContraction (quotientCoproduct (1 : Q)) = 1 := by simp

theorem h_one_both : leftContraction (quotientCoproduct (h 1)) = 0 ∧
    rightContraction (quotientCoproduct (h 1)) = 0 := by
  rw [coproduct_h]
  norm_num [Fin.sum_univ_succ, h_zero, s, EKPresentationControls.degree_one]

theorem h_two_both : leftContraction (quotientCoproduct (h 2)) = 0 ∧
    rightContraction (quotientCoproduct (h 2)) = 0 := by
  rw [coproduct_h]
  norm_num [Fin.sum_univ_succ, h_zero, s, EKPresentationControls.degree_one,
    EKPresentationControls.degree_two]
  abel

/-- The odd cross terms CANCEL, unlike ordinary tensor multiplication. -/
theorem coproduct_square : quotientCoproduct (h 1*h 1) =
    (1 : Q) ⊗ₜ[ℤ] (h 1*h 1) + (h 1*h 1) ⊗ₜ[ℤ] (1 : Q) := by
  rw [EKSignedQuotient.quotient_coproduct_mul, coproduct_h]
  simp only [map_sum, LinearMap.sum_apply, tensor_h]
  -- Keep scalars as scalars: broad norm_num rewrites integer tensor
  -- scalars to ordinary tensor-ring products, obscuring the signed formula.
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    h_zero, one_mul, mul_one, zero_add, add_zero, pow_zero, pow_one,
    one_smul, neg_one_smul]
  abel

theorem square_both : leftContraction (quotientCoproduct (h 1*h 1)) = 0 ∧
    rightContraction (quotientCoproduct (h 1*h 1)) = 0 := by
  rw [coproduct_square]
  simp [S_square_word]

/-- Mixed noncommuting control: all six actual signed tensor terms. -/
theorem coproduct_mixed : quotientCoproduct (h 2*h 1) =
    (1 : Q) ⊗ₜ[ℤ] (h 2*h 1) + h 1 ⊗ₜ[ℤ] h 2 +
    h 1 ⊗ₜ[ℤ] (h 1*h 1) - (h 1*h 1) ⊗ₜ[ℤ] h 1 +
    h 2 ⊗ₜ[ℤ] h 1 + (h 2*h 1) ⊗ₜ[ℤ] (1 : Q) := by
  rw [EKSignedQuotient.quotient_coproduct_mul, coproduct_h, coproduct_h]
  simp only [map_sum, LinearMap.sum_apply, tensor_h]
  -- Keep scalars as scalars: broad norm_num rewrites integer tensor
  -- scalars to ordinary tensor-ring products, obscuring the signed formula.
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    h_zero, one_mul, mul_one, zero_add, add_zero, pow_zero, pow_one,
    one_smul, neg_one_smul]
  abel

theorem S_mixed : S (h 2*h 1) = -h 1*(h 1*h 1-h 2) := by
  rw [S_mul (h_degree 2) (h_degree 1), S_h_one, S_h_two]
  norm_num

-- Generic polynomial simplification keeps typeclass elaboration bounded;
-- the arguments below are still the actual quotient elements h1 and h2.
private theorem mixed_left_ring {R : Type*} [Ring R] (x y : R) :
    y*x + (-x)*y + (-x)*(x*x) - (-(x*x))*x +
      (x*x-y)*x + (-x*(x*x-y)) = 0 := by noncomm_ring
private theorem mixed_right_ring {R : Type*} [Ring R] (x y : R) :
    (-x*(x*x-y)) + x*(x*x-y) + x*(-(x*x)) - (x*x)*(-x) +
      y*(-x) + y*x = 0 := by noncomm_ring

theorem mixed_both : leftContraction (quotientCoproduct (h 2*h 1)) = 0 ∧
    rightContraction (quotientCoproduct (h 2*h 1)) = 0 := by
  rw [coproduct_mixed]
  simp only [map_add, map_sub, leftContraction_tmul, rightContraction_tmul,
    S_one, S_h_one, S_h_two, S_square_word, S_mixed, one_mul, mul_one]
  exact ⟨mixed_left_ring _ _, mixed_right_ring _ _⟩

/-- The actual integral basis rejects omitting the odd reversal sign. -/
theorem ordinary_antihom_rejected : S (h 1*h 1) ≠ S (h 1)*S (h 1) := by
  rw [S_square_word, S_h_one, neg_mul_neg]
  exact EKAutomorphismsControls.super_square_not_ordinary

theorem zero_parts : S (([0,2,0,1,0].map h).prod) = e 1*e 2 := by
  simpa [h_zero, show e 0 = 1 from by simp [e],
    show Nat.choose 4 2 = 6 from rfl] using S_hWord [0,2,0,1,0]

/-- Includes nonhomogeneous elements, all degrees, and arbitrary zero-containing words. -/
theorem general_consumer (a b : ℕ) (x y z : Q) (w : List ℕ)
    (hx : x ∈ EKIntegralBases.degreePiece a) (hy : y ∈ EKIntegralBases.degreePiece b) :
    leftContraction (quotientCoproduct z) = quotientCounit z • (1 : Q) ∧
    rightContraction (quotientCoproduct z) = quotientCounit z • (1 : Q) ∧
    S (x*y) = (-1 : ℤ)^(a*b) • (S y*S x) ∧
    S x ∈ EKIntegralBases.degreePiece a ∧
    S ((w.map h).prod) = (-1 : ℤ)^((w.sum+1).choose 2) • (w.reverse.map e).prod :=
  ⟨convolution_left z, convolution_right z, S_mul hx hy, S_degree hx, S_hWord w⟩

end OddMath.Frontier.EKAntipodeControls
