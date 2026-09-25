import OddMath.Frontier.EKAutomorphismsControls

/-! EK1107.5610v2 pp20–21 Proposition 2.17, on the actual integral quotient.
The antipode is the prescribed psi1-after-psi2-after-psi3, not an abstract inverse.
Both convolution identities below use the actual signed coproduct.
Inherited source discrepancies are not silently repaired.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators TensorProduct
namespace OddMath.Frontier.EKAntipode
open EKRadicalQuotient (Q pi quotientCounit)
open EKElementaryQuotient (h e)
open EKAutomorphisms
open EKIntegralBases (degreePiece hBasis)
open EKCoideal (quotientCoproduct)
open EKSignedQuotient (quotientTensorMul)

/-- EK's exact composition order. -/
def S : Q →ₗ[ℤ] Q := psi12.toRingHom.toIntAlgHom.toLinearMap.comp psi3.toLinearMap
theorem S_apply (x : Q) : S x = psi12 (psi3 x) := rfl
@[simp] theorem S_one : S (1 : Q) = 1 := by
  have hu : psi3 (1 : Q) = 1 := by simpa [h] using psi3_h 0
  simp only [S_apply, hu, map_one]
@[simp] theorem S_h (n : ℕ) : S (h n) = s n • e n := by
  rw [S_apply, psi3_h, psi12_h]

theorem S_degree {d : ℕ} {x : Q} (hx : x ∈ degreePiece d) : S x ∈ degreePiece d :=
  psi1_degree (psi2_degree (psi3_degree hx))

theorem S_mul {a b : ℕ} {x y : Q} (hx : x ∈ degreePiece a) (hy : y ∈ degreePiece b) :
    S (x*y) = (-1 : ℤ)^(a*b) • (S y*S x) := by
  simp only [S_apply, psi3_mul hx hy, map_zsmul, map_mul]

/-- Source (2.25), for all words including zero parts and the empty word. -/
theorem S_hWord (w : List ℕ) :
    S ((w.map h).prod) = (-1 : ℤ)^((w.sum+1).choose 2) • (w.reverse.map e).prod := by
  change psi12 (psi3Linear ((w.map h).prod)) = _
  rw [psi3_word, map_zsmul, psi12_hWord, wordSign_reverse, smul_smul]
  rw [mul_assoc, wordSign_square, mul_one]
  rfl

/-- The ordinary multiplication linear map on the genuine integer tensor product. -/
def multiplication : (Q ⊗[ℤ] Q) →ₗ[ℤ] Q :=
  TensorProduct.lift (LinearMap.mul ℤ Q)
@[simp] theorem multiplication_tmul (x y : Q) : multiplication (x ⊗ₜ[ℤ] y) = x*y := rfl

def leftContraction : (Q ⊗[ℤ] Q) →ₗ[ℤ] Q :=
  multiplication.comp (TensorProduct.map S (LinearMap.id : Q →ₗ[ℤ] Q))
def rightContraction : (Q ⊗[ℤ] Q) →ₗ[ℤ] Q :=
  multiplication.comp (TensorProduct.map (LinearMap.id : Q →ₗ[ℤ] Q) S)
@[simp] theorem leftContraction_tmul (x y : Q) : leftContraction (x ⊗ₜ[ℤ] y) = S x*y := rfl
@[simp] theorem rightContraction_tmul (x y : Q) : rightContraction (x ⊗ₜ[ℤ] y) = x*S y := rfl

/-- The source inverse series relation on Q, not on a formal free surrogate. -/
theorem generator_left (n : ℕ) :
    (∑ i : Fin (n+1), S (h i)*h (n-i)) = (if n=0 then 1 else 0) := by
  cases n with
  | zero => simp [h]
  | succ n =>
    rw [if_neg (Nat.succ_ne_zero n)]
    simp only [S_h, smul_mul_assoc]
    have hh := congrArg pi (CompleteElementary.elementary_complete_inverse n)
    simpa only [ map_sum, map_mul, map_zero, CompleteElementary.ekSign,
      map_pow, map_neg, map_one, e, h, s, zsmul_eq_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, mul_assoc] using hh

/-- Applying the proved involution psi12 supplies the other inverse relation.
This does not assume that a one-sided convolution inverse is two-sided. -/
theorem generator_right (n : ℕ) :
    (∑ i : Fin (n+1), h i*S (h (n-i))) = (if n=0 then 1 else 0) := by
  have hh := congrArg psi12 (generator_left n)
  have hi (i : ℕ) : psi12 (S (h i)) = h i := by
    rw [S_apply, psi3_h, psi12_involutive]
  simp only [map_sum, map_mul, hi, psi12_h, ← S_h] at hh
  simpa only [apply_ite, map_one, map_zero] using hh

private theorem h_degree (n : ℕ) : h n ∈ degreePiece n := by
  simpa using hWord_degree [n]
private theorem basis_degree (μ : YoungDiagram) : hBasis μ ∈ degreePiece μ.card := by
  simpa only [EKIntegralBases.hBasis_apply, EKIntegralBases.rowLens_sum] using hWord_degree μ.rowLens

/-- The two Koszul signs combine independently of the generator split. -/
private theorem split_sign (n a : ℕ) (i : Fin (n+1)) :
    (-1 : ℤ)^((n-i)*a) * (-1 : ℤ)^((i : ℕ)*a) = (-1 : ℤ)^(n*a) := by
  rw [← pow_add, ← Nat.add_mul, Nat.sub_add_cancel (by omega : (i : ℕ) ≤ n)]

private theorem left_generator_tensor {a b : ℕ} {x y : Q}
    (hx : x ∈ degreePiece a) (hy : y ∈ degreePiece b) (n : ℕ) (hn : n ≠ 0) :
    leftContraction (quotientTensorMul (quotientCoproduct (h n)) (x ⊗ₜ[ℤ] y)) = 0 := by
  rw [coproduct_h, map_sum, LinearMap.sum_apply, map_sum]
  have he (i : Fin (n+1)) :
      leftContraction (quotientTensorMul (h i ⊗ₜ[ℤ] h (n-i)) (x ⊗ₜ[ℤ] y)) =
      (-1 : ℤ)^(n*a) • (S x * (S (h i)*h (n-i)) * y) := by
    rw [tensorMul_homogeneous (h_degree i) (h_degree (n-i)) hx hy,
      map_smul, leftContraction_tmul, S_mul (h_degree i) hx]
    simp only [smul_mul_assoc, smul_smul, split_sign, mul_assoc]
  simp_rw [he]
  rw [← Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum, generator_left,
    if_neg hn, mul_zero, zero_mul, smul_zero]

private theorem right_generator_tensor {a b : ℕ} {x y : Q}
    (hx : x ∈ degreePiece a) (hy : y ∈ degreePiece b) (n : ℕ) (hn : n ≠ 0) :
    rightContraction (quotientTensorMul (x ⊗ₜ[ℤ] y) (quotientCoproduct (h n))) = 0 := by
  rw [coproduct_h, map_sum, map_sum]
  have he (i : Fin (n+1)) :
      rightContraction (quotientTensorMul (x ⊗ₜ[ℤ] y) (h i ⊗ₜ[ℤ] h (n-i))) =
      (-1 : ℤ)^(n*b) • (x * (h i*S (h (n-i))) * S y) := by
    rw [tensorMul_homogeneous hx hy (h_degree i) (h_degree (n-i)),
      map_smul, rightContraction_tmul, S_mul hy (h_degree (n-i))]
    simp only [mul_smul_comm, smul_smul]
    rw [show (-1 : ℤ)^(b*(i : ℕ)) * (-1 : ℤ)^(b*(n-i)) = (-1 : ℤ)^(n*b) by
      rw [← pow_add, ← Nat.mul_add, Nat.add_sub_of_le (by omega : (i : ℕ) ≤ n), Nat.mul_comm]]
    simp only [mul_assoc]
  simp_rw [he]
  rw [← Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum, generator_right,
    if_neg hn, mul_zero, zero_mul, smul_zero]

/-- Cancellation after a positive complete generator, for EVERY actual tensor.
The basis induction supplies homogeneity; no Sweedler decomposition is assumed. -/
theorem left_generator_all (n : ℕ) (hn : n ≠ 0) (z : Q ⊗[ℤ] Q) :
    leftContraction (quotientTensorMul (quotientCoproduct (h n)) z) = 0 := by
  induction z using EKPairingAdjoint.basis_induction (hBasis.tensorProduct hBasis) with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx, hy, add_zero]
  | hb p r =>
    simp only [map_smul, Basis.tensorProduct_apply',
      left_generator_tensor (basis_degree p.1) (basis_degree p.2) n hn, smul_zero]

/-- The other cancellation, with the positive generator on the RIGHT. -/
theorem right_generator_all (n : ℕ) (hn : n ≠ 0) (z : Q ⊗[ℤ] Q) :
    rightContraction (quotientTensorMul z (quotientCoproduct (h n))) = 0 := by
  induction z using EKPairingAdjoint.basis_induction (hBasis.tensorProduct hBasis) with
  | hz => simp
  | ha x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | hb p r =>
    simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, Basis.tensorProduct_apply',
      right_generator_tensor (basis_degree p.1) (basis_degree p.2) n hn, smul_zero]

/-- Left convolution on all words, with zero letters handled as units. -/
theorem left_hWord (w : List ℕ) :
    leftContraction (quotientCoproduct ((w.map h).prod)) =
      quotientCounit ((w.map h).prod) • (1 : Q) := by
  induction w with
  | nil => simp
  | cons n w ih =>
    simp only [List.map_cons, List.prod_cons]
    by_cases hn : n=0
    · subst n
      simpa only [show h 0 = 1 from by simp [h], one_mul] using ih
    · rw [EKSignedQuotient.quotient_coproduct_mul, left_generator_all n hn,
        map_mul, counit_h, if_neg hn, zero_mul, zero_smul]

/-- Right convolution uses the LAST letter; this is not inferred from left convolution. -/
theorem right_hWord (w : List ℕ) :
    rightContraction (quotientCoproduct ((w.map h).prod)) =
      quotientCounit ((w.map h).prod) • (1 : Q) := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w n ih =>
    simp only [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
    by_cases hn : n=0
    · subst n
      simpa only [show h 0 = 1 from by simp [h], mul_one] using ih
    · rw [EKSignedQuotient.quotient_coproduct_mul, right_generator_all n hn,
        map_mul, counit_h, if_neg hn, mul_zero, zero_smul]

/-- First antipode identity, for arbitrary (also inhomogeneous) actual quotient elements. -/
theorem convolution_left (x : Q) :
    multiplication (TensorProduct.map S (LinearMap.id : Q →ₗ[ℤ] Q)
      (quotientCoproduct x)) = quotientCounit x • (1 : Q) := by
  change leftContraction (quotientCoproduct x) = _
  induction x using EKPairingAdjoint.basis_induction hBasis with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx, hy, add_smul]
  | hb μ r =>
    simp only [map_smul, EKIntegralBases.hBasis_apply]
    rw [show EKPartitionSpanning.hPartition μ = (μ.rowLens.map h).prod from rfl,
      left_hWord, smul_smul, smul_eq_mul]

/-- Second antipode identity, independently established with the signed coproduct. -/
theorem convolution_right (x : Q) :
    multiplication (TensorProduct.map (LinearMap.id : Q →ₗ[ℤ] Q) S
      (quotientCoproduct x)) = quotientCounit x • (1 : Q) := by
  change rightContraction (quotientCoproduct x) = _
  induction x using EKPairingAdjoint.basis_induction hBasis with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx, hy, add_smul]
  | hb μ r =>
    simp only [map_smul, EKIntegralBases.hBasis_apply]
    rw [show EKPartitionSpanning.hPartition μ = (μ.rowLens.map h).prod from rfl,
      right_hWord, smul_smul, smul_eq_mul]

/-- Low-degree identities used to exhibit the integral non-involutivity. -/
theorem S_h_one : S (h 1) = -h 1 := by
  rw [S_h, EKPresentationControls.degree_one]
  norm_num [s]
theorem S_h_two : S (h 2) = h 1*h 1-h 2 := by
  rw [S_h, EKPresentationControls.degree_two]
  norm_num [s]
theorem S_square_word : S (h 1*h 1) = -(h 1*h 1) := by
  have hh := S_hWord [1,1]
  simpa [EKPresentationControls.degree_one] using hh

/-- Non-involutivity witness, in Q over integers, not a free expression. -/
theorem S_square_h_two : S (S (h 2)) = h 2 - (2 : ℤ) • (h 1*h 1) := by
  rw [S_h_two, map_sub, S_square_word, S_h_two, two_smul]
  abel

theorem S_not_involutive : S (S (h 2)) ≠ h 2 := by
  rw [S_square_h_two]
  intro he
  have hz : h 1*h 1 + h 1*h 1 = 0 := by
    simpa only [two_smul] using sub_eq_self.mp he
  exact EKAutomorphismsControls.super_square_not_ordinary
    (eq_neg_of_add_eq_zero_left hz).symm

/-- Explicit two-sided consumer, for ALL elements, with no homogeneous premise. -/
theorem antipode_identities (x : Q) :
    multiplication (TensorProduct.map S (LinearMap.id : Q →ₗ[ℤ] Q) (quotientCoproduct x)) =
      quotientCounit x • (1 : Q) ∧
    multiplication (TensorProduct.map (LinearMap.id : Q →ₗ[ℤ] Q) S (quotientCoproduct x)) =
      quotientCounit x • (1 : Q) :=
  ⟨convolution_left x, convolution_right x⟩

end OddMath.Frontier.EKAntipode
