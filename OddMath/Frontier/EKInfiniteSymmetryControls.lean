import OddMath.Frontier.EKInfiniteSymmetry

/-! Test-first degree 0/1/2 controls, compiled before the production module.
Hand calculation: psi1(h2)=h2-h1², psi2(h1)=-h1, psi2(h2)=-h2.
S(h1)=-h1, S(h1²)=-h1², S(h2)=h1²-h2, hence S²(h2)=h2-2h1².
The negative square is essential; S is not an ordinary ring automorphism. -/
noncomputable section
namespace OddMath.Frontier.EKInfiniteSymmetryControls
open EKRadicalQuotient (Q)
open EKElementaryQuotient (h e)
open EKPresentation (psi1 psi1_h)
open EKAutomorphisms EKAntipode

theorem degree_zero : psi1 (h 0) = 1 ∧ psi2 (h 0) = 1 ∧ S (h 0) = 1 := by
  simp [h]

theorem degree_one : psi1 (h 1) = h 1 ∧ psi2 (h 1) = -h 1 ∧ S (h 1) = -h 1 := by
  simp [psi1_h, EKPresentationControls.degree_one, s, S_h_one]

theorem degree_two : psi1 (h 2) = h 2-h 1*h 1 ∧ psi2 (h 2) = -h 2 ∧
    S (h 2) = h 1*h 1-h 2 ∧ S (h 1*h 1) = -(h 1*h 1) := by
  simp [psi1_h, EKPresentationControls.degree_two, s, S_h_two, S_square_word]

theorem second_step : psi1 (psi1 (h 2)) = h 2-(2 : ℤ) • (h 1*h 1) ∧
    S (S (h 2)) = h 2-(2 : ℤ) • (h 1*h 1) := by
  constructor
  · rw [degree_two.1, map_sub, map_mul, degree_two.1, degree_one.1, two_smul]
    abel
  · exact S_square_h_two

-- The group convention really is pointwise composition, not reversed trans.
theorem composition_convention (a b : Q ≃+* Q) (x : Q) : (a*b) x = a (b x) := rfl

theorem source_generator_relation : psi2*psi1*psi2 = psi1⁻¹ := by
  ext x
  exact psi2_psi1_psi2 x

/-! The controls above were first compiled independently of production; that
exact source is sealed in an unpublished script with its passing receipt.
The following consumers are deliberately POST-production. -/
open EKInfiniteSymmetry

theorem inverse_rotation_control : (psi1^(-1 : ℤ)) (h 2) = h 2+h 1*h 1 := by
  simpa only [neg_one_smul, sub_neg_eq_add] using rotation_h_two (-1)

theorem reflection_order_control : rho (.sr 1) (h 2) = -h 2-h 1*h 1 := by
  simpa only [rho_sr, zpow_one, one_smul] using reflection_h_two 1

/-- All four Mathlib multiplication conventions, for arbitrary integers. -/
theorem multiplication_controls (i j : ℤ) :
    rho (.r i * .r j) = psi1^(i+j) ∧
    rho (.r i * .sr j) = psi2*psi1^(j-i) ∧
    rho (.sr i * .r j) = psi2*psi1^(i+j) ∧
    rho (.sr i * .sr j) = psi1^(j-i) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Genuine all-element consumer: unique normal form plus BOTH actual witnesses.
The h1 action separates the two tags; the h2 translation separates exponents. -/
theorem all_element_consumer (f : generated) :
    ∃! p : Bool × ℤ,
      f.val = (if p.1 then psi2*psi1^p.2 else psi1^p.2) ∧
      f.val (h 1) = (if p.1 then -h 1 else h 1) ∧
      f.val (h 2) = (if p.1 then -h 2 else h 2)-p.2 • (h 1*h 1) := by
  obtain ⟨p, hp, hu⟩ := unique_normal_form f
  refine ⟨p, ⟨hp, ?_⟩, fun q hq => hu q hq.1⟩
  rcases p with ⟨b,i⟩
  cases b with
  | false =>
    change f.val = psi1^i at hp
    change f.val (h 1) = h 1 ∧ f.val (h 2) = h 2-i • (h 1*h 1)
    rw [hp, rotation_h_one, rotation_h_two]
    exact ⟨rfl, rfl⟩
  | true =>
    change f.val = psi2*psi1^i at hp
    change f.val (h 1) = -h 1 ∧ f.val (h 2) = -h 2-i • (h 1*h 1)
    rw [hp, reflection_h_one, reflection_h_two]
    exact ⟨rfl, rfl⟩

/-- Arbitrary time indices; no finite numerical ladder substitutes for these. -/
theorem orbit_consumer (i j : ℕ) :
    ((S^[2*i]) (h 2) = (S^[2*j]) (h 2) ↔ i = j) ∧
    ((psi1^[i]) (h 2) = (psi1^[j]) (h 2) ↔ i = j) := by
  constructor
  · exact S_even_orbit_injective.eq_iff
  · constructor
    · intro he
      simp only [psi1_iterate_h_two] at he
      exact_mod_cast translation_injective he
    · rintro rfl; rfl

end OddMath.Frontier.EKInfiniteSymmetryControls
