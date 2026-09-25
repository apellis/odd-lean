import OddMath.Frontier.NilCoxeterWords

/-! EKL1111.1320v1 (2.41)–(2.43) and the left-operator independence
part of Proposition 2.11. The printed inverse selector in (2.43) is not
silently adopted: with (2.41) and rightmost-first composition it is w=u. -/
namespace OddMath.Frontier.OddSchubertAction
open NilCoxeterWords LongestElementary
open OddMath.SkewPolynomial (SkewPolynomial monomial)
open scoped BigOperators
noncomputable section

/-- Literal (2.41), retaining the inherited chosen reduced word. -/
def schubert {n : ℕ} (w : Perm n) : SkewPolynomial (n+2) :=
  dividedElementOperator (w⁻¹ * longest (n+2)) (LongestDivided.staircase (n+2))

@[simp] theorem length_inv {n : ℕ} (p : Perm n) : length p⁻¹ = length p := by
  classical
  unfold length
  have hs (f : Fin (n+2) → ℕ) := Equiv.sum_comp p f
  calc
    _ = ∑ a : Fin (n+2), ∑ b : Fin (n+2),
        if p a < p b ∧ b < a then 1 else 0 := by
      rw [← hs (fun a => ∑ b : Fin (n+2), if a < b ∧ p⁻¹ b < p⁻¹ a then 1 else 0)]
      apply Finset.sum_congr rfl
      intro a _
      rw [← hs (fun b => if p a < b ∧ p⁻¹ b < p⁻¹ (p a) then 1 else 0)]
      simp
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [and_comm]

@[simp] theorem longest_inv (N : ℕ) : (longest N)⁻¹ = longest N := by
  exact inv_eq_of_mul_eq_one_right (longest_involutive N)

@[simp] theorem length_longest (n : ℕ) : length (longest (n+2)) = (n+2).choose 2 := by
  rw [← sourceWord_permutation n, ← sourceWord_reduced, sourceWord_length]

theorem length_longest_mul {n : ℕ} (p : Perm n) :
    length (longest (n+2) * p) + length p = (n+2).choose 2 := by
  rw [← length_longest]
  unfold length
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Equiv.Perm.mul_apply, longest_apply, Fin.rev_lt_rev]
  have hn : a ≠ b → p a ≠ p b := fun h he => h (p.injective he)
  split_ifs <;> omega

theorem length_mul_longest {n : ℕ} (p : Perm n) :
    length (p * longest (n+2)) + length p = (n+2).choose 2 := by
  have h := length_longest_mul p⁻¹
  simpa only [← length_inv (p * longest (n+2)), mul_inv_rev, longest_inv,
    length_inv] using h

theorem complement_length {n : ℕ} (w : Perm n) :
    length (w⁻¹ * longest (n+2)) + length w = (n+2).choose 2 := by
  simpa only [length_inv] using length_mul_longest w⁻¹

/-- Integer-safe form of the length condition in (2.42). -/
theorem action_length_iff {n : ℕ} (u w : Perm n) :
    length (u * (w⁻¹ * longest (n+2))) = length u + length (w⁻¹ * longest (n+2)) ↔
      length (w * u⁻¹) + length u = length w := by
  have h₁ := complement_length w
  have h₂ := complement_length (w*u⁻¹)
  simp only [mul_inv_rev, inv_inv, mul_assoc] at h₂
  omega

/-- The nonzero branch of (2.42), with a single integral sign. -/
theorem action_additive {n : ℕ} (u w : Perm n)
    (h : length (w*u⁻¹) + length u = length w) :
    Signed (dividedElementOperator u (schubert w)) (schubert (w*u⁻¹)) := by
  have hs := dividedElementOperator_mul_additive u (w⁻¹ * longest (n+2))
    ((action_length_iff u w).mpr h)
  rcases hs with hs | hs
  · left
    simpa only [schubert, mul_inv_rev, inv_inv, mul_assoc] using
      congrArg (fun L : Module.End ℤ (SkewPolynomial (n+2)) => L (LongestDivided.staircase (n+2))) hs
  · right
    simpa only [schubert, mul_inv_rev, inv_inv, mul_assoc] using
      congrArg (fun L : Module.End ℤ (SkewPolynomial (n+2)) => L (LongestDivided.staircase (n+2))) hs

/-- The zero branch; no truncated natural subtraction is used. -/
theorem action_nonadditive {n : ℕ} (u w : Perm n)
    (h : length (w*u⁻¹) + length u ≠ length w) :
    dividedElementOperator u (schubert w) = 0 := by
  have hs := dividedElementOperator_mul_nonadditive u (w⁻¹ * longest (n+2))
    (fun he => h ((action_length_iff u w).mp he))
  exact congrArg (fun L : Module.End ℤ (SkewPolynomial (n+2)) => L (LongestDivided.staircase (n+2))) hs

theorem action_shorter {n : ℕ} (u w : Perm n) (h : length w < length u) :
    dividedElementOperator u (schubert w) = 0 :=
  action_nonadditive u w (by omega)

@[simp] theorem length_eq_zero {n : ℕ} (p : Perm n) : length p = 0 ↔ p = 1 := by
  constructor
  · intro hp
    apply eq_one_of_no_descent
    intro i hi
    have := length_descend p i hi
    omega
  · rintro rfl
    exact length_one n

/-- Lemma 2.10 after the allowed chosen-word global sign. -/
theorem schubert_one_signed (n : ℕ) : Signed (schubert (1 : Perm n)) 1 := by
  obtain ⟨ε, hε, _, hop⟩ := chosen_longest_source_sign n
  have he : schubert (1 : Perm n) = ε • ((-1 : ℤ)^((n+2).choose 3) • (1 : SkewPolynomial (n+2))) := by
    simp only [schubert, inv_one, one_mul, hop, LinearMap.smul_apply, LongestDivided.D_staircase]
  rcases hε with rfl | rfl <;>
    rcases neg_one_pow_eq_or ℤ ((n+2).choose 3) with h | h <;>
    simp only [h, one_smul, neg_one_smul, neg_neg] at he
  · exact Or.inl he
  · exact Or.inr he
  · exact Or.inr he
  · exact Or.inl he

theorem action_self {n : ℕ} (w : Perm n) :
    Signed (dividedElementOperator w (schubert w)) 1 := by
  have h := action_additive w w (by simp)
  simp only [mul_inv_cancel] at h
  exact h.trans (schubert_one_signed n)

/-- The consistent equal-length selector is w=u, NOT the printed w=u⁻¹. -/
theorem action_same_length_distinct {n : ℕ} (u w : Perm n)
    (hl : length w = length u) (hne : w ≠ u) :
    dividedElementOperator u (schubert w) = 0 := by
  apply action_nonadditive
  intro h
  have hz : length (w*u⁻¹) = 0 := by omega
  exact hne (mul_inv_eq_one.mp ((length_eq_zero _).mp hz))

theorem action_same_length {n : ℕ} (u w : Perm n) (hl : length w = length u) :
    (w = u ∧ Signed (dividedElementOperator u (schubert w)) 1) ∨
      (w ≠ u ∧ dividedElementOperator u (schubert w) = 0) := by
  by_cases h : w = u
  · subst w
    exact Or.inl ⟨rfl, action_self u⟩
  · exact Or.inr ⟨h, action_same_length_distinct u w hl h⟩

/-- The actual LEFT operators in the first family of (2.39). -/
def leftOperator {n : ℕ} (i : (Fin (n+2) → ℕ) × Perm n) :
    Module.End ℤ (SkewPolynomial (n+2)) :=
  (LinearMap.mulLeft ℤ (monomial i.1 1)).comp (dividedElementOperator i.2)

@[simp] theorem leftOperator_apply {n : ℕ} (i : (Fin (n+2) → ℕ) × Perm n)
    (f : SkewPolynomial (n+2)) :
    leftOperator i f = monomial i.1 1 * dividedElementOperator i.2 f := rfl

/-- Proposition 2.11, LEFT family: arbitrary finite integral relation,
proved by increasing divided-word length and actual PBW coefficients. -/
theorem left_relation_coefficients {n : ℕ}
    (s : Finset ((Fin (n+2) → ℕ) × Perm n))
    (c : ((Fin (n+2) → ℕ) × Perm n) → ℤ)
    (h : ∀ f : SkewPolynomial (n+2), ∑ i ∈ s, c i • leftOperator i f = 0) :
    ∀ i ∈ s, c i = 0 := by
  classical
  have claim : ∀ k, ∀ i ∈ s, length i.2 = k → c i = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hi hik
      have he := congrArg (fun f : SkewPolynomial (n+2) => f i.1) (h (schubert i.2))
      simp only [Finsupp.finset_sum_apply, Finsupp.zero_apply] at he
      have hz (j) (hj : j ∈ s) (hji : j ≠ i) :
          (c j • leftOperator j (schubert i.2)) i.1 = 0 := by
        by_cases hlt : length j.2 < length i.2
        · rw [ih (length j.2) (by omega) j hj rfl, zero_smul, Finsupp.zero_apply]
        · by_cases hp : j.2 = i.2
          · have ha : j.1 ≠ i.1 := fun hh => hji (Prod.ext hh hp)
            rcases action_self i.2 with hs | hs <;>
              simp [leftOperator_apply, hp, hs, monomial, Finsupp.single_apply, ha, Ne.symm ha]
          · have hop : dividedElementOperator j.2 (schubert i.2) = 0 := by
              by_cases heq : length i.2 = length j.2
              · exact action_same_length_distinct j.2 i.2 heq (Ne.symm hp)
              · exact action_shorter j.2 i.2 (by omega)
            simp [leftOperator_apply, hop]
      rw [Finset.sum_eq_single i hz (fun hn => (hn hi).elim)] at he
      rcases action_self i.2 with hs | hs <;>
        simpa [leftOperator_apply, hs, monomial] using he
  intro i hi
  exact claim (length i.2) i hi rfl

/-- No spanning, polynomial-basis or faithfulness hypothesis is assumed. -/
theorem leftOperator_linearIndependent (n : ℕ) :
    LinearIndependent ℤ (leftOperator (n := n)) := by
  apply linearIndependent_iff'.mpr
  intro s c h
  apply left_relation_coefficients s c
  intro f
  have he := congrArg (fun L : Module.End ℤ (SkewPolynomial (n+2)) => L f) h
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] using he

/-- An explicit vanishing iff for arbitrary finite-support LEFT relations. -/
theorem left_relation_iff {n : ℕ}
    (c : ((Fin (n+2) → ℕ) × Perm n) →₀ ℤ) :
    (∀ f : SkewPolynomial (n+2),
      c.sum (fun i a => a • (monomial i.1 1 * dividedElementOperator i.2 f)) = 0) ↔ c = 0 := by
  constructor
  · intro h
    have hc := left_relation_coefficients c.support c h
    ext i
    by_cases hi : i ∈ c.support
    · exact hc i hi
    · exact Finsupp.not_mem_support_iff.mp hi
  · rintro rfl
    simp

/-- The all-permutation Schubert polynomials are integrally independent.
This uses decreasing Schubert length, not a claim of spanning. -/
theorem schubert_linearIndependent (n : ℕ) :
    LinearIndependent ℤ (schubert (n := n)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c h
  have claim : ∀ k, ∀ w ∈ s, (n+2).choose 2 - length w = k → c w = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro w hw hwk
      have he := congrArg (dividedElementOperator w) h
      simp only [map_sum, map_smul, map_zero] at he
      have hz (v) (hv : v ∈ s) (hvw : v ≠ w) :
          c v • dividedElementOperator w (schubert v) = 0 := by
        by_cases hlt : length w < length v
        · have hb := length_le_max v
          rw [ih ((n+2).choose 2 - length v) (by omega) v hv rfl, zero_smul]
        · have hop : dividedElementOperator w (schubert v) = 0 := by
            by_cases hl : length v = length w
            · exact action_same_length_distinct w v hl hvw
            · exact action_shorter w v (by omega)
          rw [hop, smul_zero]
      rw [Finset.sum_eq_single w hz (fun hn => (hn hw).elim)] at he
      rcases action_self w with hs | hs
      · rw [hs] at he
        have hc := congrArg (fun f : SkewPolynomial (n+2) => f 0) he
        change (c w • Finsupp.single (0 : Fin (n+2) → ℕ) (1 : ℤ)) 0 = 0 at hc
        simpa only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] using hc
      · rw [hs] at he
        have hc := congrArg (fun f : SkewPolynomial (n+2) => f 0) he
        change (c w • -Finsupp.single (0 : Fin (n+2) → ℕ) (1 : ℤ)) 0 = 0 at hc
        simpa only [Finsupp.smul_apply, Finsupp.neg_apply, Finsupp.single_eq_same,
          smul_eq_mul, mul_neg, mul_one, neg_eq_zero] using hc
  intro w hw
  exact claim _ w hw rfl

end
end OddMath.Frontier.OddSchubertAction
