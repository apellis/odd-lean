import OddMath.Frontier.EKIntegralBasesControls
import OddMath.Frontier.EKPresentation

/-! EK Cor2.13 preproduction sign controls on inherited objects.
Ordered e*h recurrence: e2=h2-h1²; e3=-h3+h1h2+h2h1-h1³.
Only after the odd relation may e3 simplify to h3-h1³. -/
noncomputable section
set_option maxRecDepth 3000
namespace OddMath.Frontier.EKPresentationControls
open EKRadicalQuotient EKElementaryQuotient

theorem degree_zero : h 0 = 1 ∧ e 0 = 1 := by simp [h, e]
theorem degree_one : e 1 = h 1 := by
  simp [e, h, CompleteElementary.elementary, CompleteElementary.ekSign,
    CompleteElementary.inverseCoeff, Fin.sum_univ_succ]
theorem degree_two : e 2 = h 2 - h 1 * h 1 :=
  EKIntegralBasesControls.elementary_two

theorem degree_three_ordered :
    e 3 = -h 3 + h 1*h 2 + h 2*h 1 - h 1*h 1*h 1 := by
  have hh := congrArg pi (CompleteElementary.elementary_complete_inverse 2)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    Fin.val_succ, map_add, map_mul, map_zero] at hh
  norm_num [CompleteElementary.ekSign, show Nat.choose 4 2 = 6 from rfl] at hh
  change h 3 + (-(e 1*h 2) + (-(e 2*h 1) + e 3)) = 0 at hh
  rw [degree_one, degree_two, sub_mul] at hh
  apply sub_eq_zero.mp
  convert hh using 1
  abel

theorem degree_three : e 3 = h 3 - h 1*h 1*h 1 := by
  rw [degree_three_ordered, EKIntegralBasesControls.degree_three_sign]
  simp only [two_smul]
  abel

theorem noncommuting_control : h 1*h 2 ≠ h 2*h 1 :=
  EKIntegralBasesControls.wrong_degree_three_swap_rejected

theorem wrong_degree_two_sign : e 2 ≠ h 2 + h 1*h 1 :=
  EKIntegralBasesControls.wrong_elementary_sign_rejected

/-- Any ring endomorphism with the required generator images fails involutivity.
This is a preproduction negative control, not yet an existence assertion. -/
theorem prescribed_map_not_involutive (f : Q →+* Q)
    (hf : ∀ n, f (h n) = e n) : f (f (h 2)) ≠ h 2 := by
  rw [hf, degree_two, map_sub, map_mul, hf, hf, degree_one, degree_two]
  intro hh
  have he : h 2 - h 1*h 1 = h 2 + h 1*h 1 :=
    (sub_eq_iff_eq_add.mp hh)
  exact wrong_degree_two_sign (degree_two.trans he)

/-! POSTPRODUCTION controls begin here. The earlier tests were first checked
without importing EKPresentation; their timestamped receipts are preserved. -/
open EKPresentation (psi1)

theorem psi1_degree_two : psi1 (h 2) = h 2 - h 1*h 1 := by
  rw [EKPresentation.psi1_h, degree_two]

theorem psi1_square_degree_two : psi1 (psi1 (h 2)) = h 2 - (2 : ℤ) • (h 1*h 1) := by
  rw [psi1_degree_two, map_sub, map_mul, psi1_degree_two,
    EKPresentation.psi1_h, degree_one]
  simp only [two_smul]
  abel

theorem psi1_not_involutive : psi1 (psi1 (h 2)) ≠ h 2 :=
  prescribed_map_not_involutive psi1.toRingHom EKPresentation.psi1_h

theorem psi1_inverse_degree_two : psi1.symm (h 2) = h 2 + h 1*h 1 := by
  apply psi1.injective
  rw [RingEquiv.apply_symm_apply, map_add, map_mul, psi1_degree_two,
    EKPresentation.psi1_h, degree_one]
  abel

theorem inverse_not_same : psi1.symm (h 2) ≠ psi1 (h 2) := by
  rw [psi1_inverse_degree_two, EKPresentation.psi1_h]
  exact Ne.symm wrong_degree_two_sign

theorem psi1_noncommuting_products :
    psi1 (h 1*h 2) = e 1*e 2 ∧ psi1 (h 1*h 2) ≠ psi1 (h 2*h 1) := by
  constructor
  · simp only [map_mul, EKPresentation.psi1_h]
  · exact fun he => noncommuting_control (psi1.injective he)

/-- Includes arbitrary length, zero letters, order, both inverse laws and
multiplication in Q; no graded or finite-rank premise is introduced. -/
theorem arbitrary_word_consumer (u v : List ℕ) (x : Q) :
    psi1 (((u++v).map h).prod) = (u.map e).prod * (v.map e).prod ∧
      psi1.symm (psi1 x) = x ∧ psi1 (psi1.symm x) = x := by
  constructor
  · rw [EKPresentation.psi1_word, List.map_append, List.prod_append]
  · exact ⟨psi1.symm_apply_apply x, psi1.apply_symm_apply x⟩

/-- A boundary odd relator in the PRESENTED quotient, before mapping to Q. -/
theorem presented_boundary :
    EKPresentation.h 1*EKPresentation.h 2 + EKPresentation.h 2*EKPresentation.h 1 =
      (2 : ℤ) • EKPresentation.h 3 := by
  have hh := EKPresentation.complete_odd 0 3 (by decide) (by decide)
  simpa only [EKPresentation.h_zero, one_mul, mul_one, pow_zero, one_smul,
    Nat.zero_add, two_smul] using hh.symm

end OddMath.Frontier.EKPresentationControls
