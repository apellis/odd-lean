import OddMath.Frontier.EKPresentationControls
import OddMath.Frontier.EKAutomorphisms

/-! Preproduction controls: prescribed images do not assert existence/descent. -/
noncomputable section
namespace OddMath.Frontier.EKAutomorphismsControls
open EKRadicalQuotient EKElementaryQuotient
open EKPresentation (psi1 psi1_h)

theorem generator_signs :
    (-1 : ℤ)^((0+1).choose 2) = 1 ∧
    (-1 : ℤ)^((1+1).choose 2) = -1 ∧
    (-1 : ℤ)^((2+1).choose 2) = -1 ∧
    (-1 : ℤ)^((3+1).choose 2) = 1 ∧
    (-1 : ℤ)^((4+1).choose 2) = 1 := by decide

theorem super_square_not_ordinary : -(h 1*h 1) ≠ h 1*h 1 := by
  intro he
  have hh := congrArg (fun x : Q => EKIntegralBases.hBasis.repr x EKIntegralBasesControls.col2) he
  dsimp only at hh
  rw [← EKIntegralBasesControls.col2_value, map_neg,
    EKIntegralBases.h_coordinates_partition] at hh
  simp at hh

theorem prescribed_super_square (f : Q →ₗ[ℤ] Q)
    (hf : f (h 1*h 1) = (-1 : ℤ)^(1*1) • (f (h 1)*f (h 1)))
    (h1 : f (h 1) = h 1) : f (h 1*h 1) = -(h 1*h 1) ∧ f (h 1*h 1) ≠ h 1*h 1 := by
  have he : f (h 1*h 1) = -(h 1*h 1) := by simpa [h1] using hf
  exact ⟨he, he ▸ super_square_not_ordinary⟩

theorem prescribed_psi12_two (f : Q →+* Q)
    (hf : ∀ n, f (h n) = (-1 : ℤ)^((n+1).choose 2) • e n) :
    f (h 2) = -e 2 ∧ f (e 2) = -h 2 := by
  constructor
  · simpa using hf 2
  · rw [EKPresentationControls.degree_two, map_sub, map_mul, hf, hf]
    norm_num [EKPresentationControls.degree_one, EKPresentationControls.degree_two]

theorem prescribed_order (f : Q →+* Q)
    (hf : ∀ n, f (h n) = (-1 : ℤ)^((n+1).choose 2) • e n) :
    f (h 1*h 2) = e 1*e 2 ∧ e 1*e 2 ≠ e 2*e 1 := by
  constructor
  · rw [map_mul, hf, hf]; norm_num
  · intro he
    apply EKPresentationControls.noncommuting_control
    apply psi1.injective
    simpa only [map_mul, psi1_h] using he

/-! Postproduction controls: the prescribed maps above are now instantiated.
The preproduction passing receipt predates EKAutomorphisms.lean. -/
open EKAutomorphisms
open scoped BigOperators TensorProduct

theorem psi2_generator_controls :
    psi2 (h 0) = 1 ∧ psi2 (h 1) = -h 1 ∧ psi2 (h 2) = -h 2 ∧
      psi2 (h 3) = h 3 ∧ psi2 (h 4) = h 4 := by
  simp only [psi2_h]
  norm_num [s, h, show Nat.choose 4 2 = 6 from rfl,
    show Nat.choose 5 2 = 10 from rfl]

theorem psi3_generator_controls :
    psi3 (h 0) = 1 ∧ psi3 (h 1) = h 1 ∧ psi3 (h 2) = h 2 ∧
      psi3 (h 3) = h 3 ∧ psi3 (h 4) = h 4 := by
  simp only [psi3_h]
  simp [h]

theorem super_square : psi3 (h 1*h 1) = -(h 1*h 1) := by
  have hh := psi3_hWord [1,1]
  simpa [pairExponent] using hh

theorem ordinary_reversal_rejected : psi3 (h 1*h 1) ≠ h 1*h 1 := by
  rw [super_square]
  exact super_square_not_ordinary

theorem psi3_reverses_noncommuting_word :
    psi3 (h 2*h 1) = h 1*h 2 ∧ psi3 (h 2*h 1) ≠ h 2*h 1 := by
  have hh : psi3 (h 2*h 1) = h 1*h 2 := by
    simpa [pairExponent] using psi3_hWord [2,1]
  exact ⟨hh, hh ▸ EKPresentationControls.noncommuting_control⟩

theorem psi12_two : psi12 (h 2) = -e 2 ∧ psi12 (e 2) = -h 2 :=
  prescribed_psi12_two psi12.toRingHom psi12_h

theorem psi12_noncommuting_product :
    psi12 (h 1*h 2) = e 1*e 2 ∧ psi12 (h 1*h 2) ≠ e 2*e 1 := by
  obtain ⟨hh, hn⟩ := prescribed_order psi12.toRingHom psi12_h
  exact ⟨hh, hh ▸ hn⟩

theorem inhomogeneous_control :
    psi3 (1+h 1+h 1*h 1+h 2*h 1) = 1+h 1-h 1*h 1+h 1*h 2 := by
  have hu : psi3 (1 : Q) = 1 := by simpa [h] using psi3_h 0
  rw [map_add, map_add, map_add, hu, psi3_h, super_square,
    psi3_reverses_noncommuting_word.1]
  rfl

/-- Genuine arbitrary-degree and arbitrary-element consumer, not finite tests. -/
theorem general_consumer (a b : ℕ) (x y z : Q)
    (hx : x ∈ EKIntegralBases.degreePiece a) (hy : y ∈ EKIntegralBases.degreePiece b) :
    psi3 (x*y) = (-1 : ℤ)^(a*b) • (psi3 y*psi3 x) ∧
    psi3 (psi3 z) = z ∧ psi12 (psi12 z) = z ∧
    EKCoideal.quotientCoproduct (psi1 z) = psi1Tensor (EKCoideal.quotientCoproduct z) ∧
    quotientCounit (psi1 z) = quotientCounit z :=
  ⟨psi3_mul hx hy, psi3_involutive z, psi12_involutive z, psi1_coproduct z, psi1_counit z⟩

/-- Boundary zero parts do not introduce phantom generators. -/
theorem zero_part_words :
    psi12 (([0,1,0,2,0].map h).prod) = e 1*e 2 ∧
    psi3 (([0,1,0,1,0].map h).prod) = -(h 1*h 1) := by
  constructor
  · simpa [h] using psi12_noncommuting_product.1
  · simpa [h] using super_square

/-- Diagnostic character witnesses genuine integral nonzero signs. -/
private def oneCharacter : Q →+* ℤ := descend (fun _ => (1 : ℤ)) rfl
  (by intros; simp) (by intros; simp [add_comm])
private theorem oneCharacter_h (n : ℕ) : oneCharacter (h n) = 1 := descend_h _ _ _ _ n

/-- The retained PDF literally prints λ_j λ_j in (2.24). At [2,1]
that predicts the NEGATIVE of its own preceding displayed example. -/
theorem literal_printed_224_counterexample : psi3 (h 2*h 1) ≠ -(h 1*h 2) := by
  rw [psi3_reverses_noncommuting_word.1]
  intro hh
  have he := congrArg oneCharacter hh
  simp only [map_mul, map_neg, oneCharacter_h, mul_one] at he
  norm_num at he

/-- p19 explicitly says psi3 does not fix e_n. This diagnoses the omitted
transformation in p21's 'Applying psi3 to (2.5)' explanation of (2.26). -/
theorem psi3_e_two : psi3 (e 2) = h 2 + h 1*h 1 := by
  rw [EKPresentationControls.degree_two, map_sub, psi3_h, super_square, sub_neg_eq_add]

theorem psi3_e_two_not_fixed : psi3 (e 2) ≠ e 2 := by
  intro hh
  rw [psi3_e_two, EKPresentationControls.degree_two, sub_eq_add_neg] at hh
  exact super_square_not_ordinary (add_left_cancel hh).symm

theorem direct_226_term_mismatch :
    psi3 ((-1 : ℤ) • (e 1*h 1)) ≠ (-1 : ℤ) • (h 1*e 1) := by
  rw [EKPresentationControls.degree_one, map_smul, super_square]
  simpa using Ne.symm super_square_not_ordinary

end OddMath.Frontier.EKAutomorphismsControls
