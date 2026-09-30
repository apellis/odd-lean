import OddMath.Frontier.QuantumSl2Plus

/-!
# Quantum binomial coefficients at `q = √−1`

Ellis–Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2, §2.1: the structure
constants of `U⁺ = U⁺_{√−1}(sl₂)` are the quantum binomial coefficients `[a+b, a]` "evaluated at
`q = √−1`, in `ℤ[√−1]`" (text after (2.1)).

We work with Lusztig's integral form over `A = ℤ[q, q⁻¹]` from `QuantumSl2Plus`
(`qBinom a b = [a+b, a]`, balanced) and specialise along the ring map
`evI : ℤ[q, q⁻¹] → ℤ[√−1]`, `q ↦ √−1` (`GaussianInt`).

* `qBinom_eval_of_sq`: for every ring map `ψ : A → R` with `ψ(q²) = −1`,
  `ψ [a+b, a] = ψ(q^{-ab}) · β(a, b)` where `β(a, b) = 0` if `a` and `b` are both odd and
  `β(a, b) = C(⌊(a+b)/2⌋, ⌊a/2⌋)` otherwise (`binomNegOne`; this is the Gaussian binomial
  `(a+b choose a)_{q²}` at `q² = −1`).
* `evI_qBinom`: `[a+b, a]_{q=√−1} = (−√−1)^{ab} β(a, b)`.
* `evI_qBinom_eq_zero_iff`: `[a+b, a]_{q=√−1} = 0` **iff `a` and `b` are both odd**.
  The printed sentence "In particular, it is zero if `a + b` is even" is false
  (`printed_zero_claim_false`: `[4, 2]_{q=√−1} = 2`, `evI_qBinom_two_two`).
* `evJ_qBinom`: the specialisation at `q = −√−1` gives the same binomials (bar invariance).
-/

namespace OddMath.Frontier.EQQuantum
open Finset LaurentPolynomial QuantumSl2Plus

local notation "A" => LaurentPolynomial ℤ

/-! ### `√−1` and the specialisation `q ↦ √−1` -/

/-- `√−1 = ⟨0, 1⟩ ∈ ℤ[√−1]`. -/
def ii : GaussianInt := ⟨0, 1⟩

theorem ii_mul_ii : ii * ii = -1 := by decide

/-- `√−1` as a unit of `ℤ[√−1]`. -/
def iiUnit : GaussianIntˣ := ⟨ii, -ii, by decide, by decide⟩

/-- `-√−1` as a unit of `ℤ[√−1]`. -/
def iiUnitNeg : GaussianIntˣ := ⟨-ii, ii, by decide, by decide⟩

theorem ii_ne_zero : ii ≠ 0 := by decide

/-- The specialisation `ℤ[q, q⁻¹] → ℤ[√−1]`, `q ↦ √−1`. -/
noncomputable def evI : A →+* GaussianInt := eval₂ (Int.castRingHom GaussianInt) iiUnit

/-- The specialisation `ℤ[q, q⁻¹] → ℤ[√−1]`, `q ↦ −√−1`. -/
noncomputable def evJ : A →+* GaussianInt := eval₂ (Int.castRingHom GaussianInt) iiUnitNeg

theorem evI_T_nat (n : ℕ) : evI (T n) = ii ^ n := by
  rw [evI, eval₂_T_n]; rfl

theorem evI_T_neg_nat (n : ℕ) : evI (T (-(n : ℤ))) = (-ii) ^ n := by
  rw [evI, eval₂_T_neg_n]; rfl

theorem evJ_T_nat (n : ℕ) : evJ (T n) = (-ii) ^ n := by
  rw [evJ, eval₂_T_n]; rfl

theorem evJ_T_neg_nat (n : ℕ) : evJ (T (-(n : ℤ))) = ii ^ n := by
  rw [evJ, eval₂_T_neg_n]; rfl

theorem evI_T_two : evI (T 2) = -1 := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, evI_T_nat]; decide

theorem evJ_T_two : evJ (T 2) = -1 := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, evJ_T_nat]; decide

/-- The braiding parameter `q^{-2}` of the EKL `q`-bialgebra specialises to `−1` at `q = √−1`. -/
theorem evI_T_neg_two : evI (T (-2)) = -1 := by
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) from rfl, evI_T_neg_nat]; decide

theorem evJ_T_neg_two : evJ (T (-2)) = -1 := by
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) from rfl, evJ_T_neg_nat]; decide

/-- The printed twist parameter: `v = √−1 = evI(q)`. -/
theorem evI_T_one : evI (T 1) = ii := by
  simpa using evI_T_nat 1

/-- `[2] = q + q⁻¹` vanishes at `q = √−1` (the display after (2.2)). -/
theorem evI_qInt_two : evI (qInt 2) = 0 := by
  simp only [qInt, sum_range_succ, range_zero, sum_empty, zero_add, map_add]
  rw [show ((2 : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ) = ((1 : ℕ) : ℤ) by norm_num,
    show ((2 : ℕ) : ℤ) - 1 - 2 * ((1 : ℕ) : ℤ) = -((1 : ℕ) : ℤ) by norm_num, evI_T_nat,
    evI_T_neg_nat]
  ring

/-! ### Gaussian binomials at `q² = −1` -/

/-- The Gaussian binomial `(a+b choose a)_{x}` at `x = −1`: `0` if `a` and `b` are both odd, and
`C(⌊(a+b)/2⌋, ⌊a/2⌋)` otherwise. -/
def binomNegOne (a b : ℕ) : ℕ := if Odd a ∧ Odd b then 0 else Nat.choose ((a + b) / 2) (a / 2)

theorem binomNegOne_zero_left (b : ℕ) : binomNegOne 0 b = 1 := by
  simp [binomNegOne]

theorem binomNegOne_zero_right (a : ℕ) : binomNegOne a 0 = 1 := by
  simp [binomNegOne]

theorem binomNegOne_of_odd {a b : ℕ} (h : Odd a ∧ Odd b) : binomNegOne a b = 0 := by
  simp [binomNegOne, h]

theorem binomNegOne_of_not {a b : ℕ} (h : ¬ (Odd a ∧ Odd b)) :
    binomNegOne a b = Nat.choose ((a + b) / 2) (a / 2) := by
  simp only [binomNegOne, h, ite_false]

theorem binomNegOne_eq_zero_iff (a b : ℕ) : binomNegOne a b = 0 ↔ Odd a ∧ Odd b := by
  unfold binomNegOne
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (Nat.choose_pos (by omega)).ne' h

/-- The `q = −1` Pascal recursion `β(a+1, b+1) = β(a+1, b) + (−1)^{b+1} β(a, b+1)`. -/
theorem binomNegOne_rec (a b : ℕ) :
    (binomNegOne (a + 1) (b + 1) : ℤ) =
      binomNegOne (a + 1) b + (-1) ^ (b + 1) * binomNegOne a (b + 1) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' a <;> obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' b
  · -- a, b even
    have h1 : Odd (2 * m + 1) ∧ Odd (2 * n + 1) := ⟨odd_two_mul_add_one m, odd_two_mul_add_one n⟩
    have h2 : ¬ (Odd (2 * m + 1) ∧ Odd (2 * n)) := fun h => by
      exact (Nat.not_odd_iff_even.2 (even_two_mul n)) h.2
    have h3 : ¬ (Odd (2 * m) ∧ Odd (2 * n + 1)) := fun h => by
      exact (Nat.not_odd_iff_even.2 (even_two_mul m)) h.1
    rw [binomNegOne_of_odd h1, binomNegOne_of_not h2, binomNegOne_of_not h3]
    rw [show (2 * m + 1 + 2 * n) / 2 = m + n by omega, show (2 * m + 1) / 2 = m by omega,
      show (2 * m + (2 * n + 1)) / 2 = m + n by omega, show 2 * m / 2 = m by omega,
      pow_succ, pow_mul]
    norm_num
  · -- a even, b odd
    have h1 : ¬ (Odd (2 * m + 1) ∧ Odd (2 * n + 1 + 1)) := fun h => by
      rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring] at h
      exact (Nat.not_odd_iff_even.2 (even_two_mul _)) h.2
    have h2 : Odd (2 * m + 1) ∧ Odd (2 * n + 1) := ⟨odd_two_mul_add_one m, odd_two_mul_add_one n⟩
    have h3 : ¬ (Odd (2 * m) ∧ Odd (2 * n + 1 + 1)) := fun h => by
      exact (Nat.not_odd_iff_even.2 (even_two_mul m)) h.1
    rw [binomNegOne_of_odd h2, binomNegOne_of_not h1, binomNegOne_of_not h3]
    rw [show (2 * m + 1 + (2 * n + 1 + 1)) / 2 = m + n + 1 by omega,
      show (2 * m + 1) / 2 = m by omega, show (2 * m + (2 * n + 1 + 1)) / 2 = m + n + 1 by omega,
      show 2 * m / 2 = m by omega, show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul]
    norm_num
  · -- a odd, b even
    have h1 : ¬ (Odd (2 * m + 1 + 1) ∧ Odd (2 * n + 1)) := fun h => by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring] at h
      exact (Nat.not_odd_iff_even.2 (even_two_mul _)) h.1
    have h2 : ¬ (Odd (2 * m + 1 + 1) ∧ Odd (2 * n)) := fun h => by
      exact (Nat.not_odd_iff_even.2 (even_two_mul n)) h.2
    have h3 : Odd (2 * m + 1) ∧ Odd (2 * n + 1) := ⟨odd_two_mul_add_one m, odd_two_mul_add_one n⟩
    rw [binomNegOne_of_odd h3, binomNegOne_of_not h1, binomNegOne_of_not h2]
    rw [show (2 * m + 1 + 1 + (2 * n + 1)) / 2 = m + n + 1 by omega,
      show (2 * m + 1 + 1) / 2 = m + 1 by omega,
      show (2 * m + 1 + 1 + 2 * n) / 2 = m + n + 1 by omega]
    norm_num
  · -- a, b odd
    have h1 : ¬ (Odd (2 * m + 1 + 1) ∧ Odd (2 * n + 1 + 1)) := fun h => by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring] at h
      exact (Nat.not_odd_iff_even.2 (even_two_mul _)) h.1
    have h2 : ¬ (Odd (2 * m + 1 + 1) ∧ Odd (2 * n + 1)) := fun h => by
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring] at h
      exact (Nat.not_odd_iff_even.2 (even_two_mul _)) h.1
    have h3 : ¬ (Odd (2 * m + 1) ∧ Odd (2 * n + 1 + 1)) := fun h => by
      rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring] at h
      exact (Nat.not_odd_iff_even.2 (even_two_mul _)) h.2
    rw [binomNegOne_of_not h1, binomNegOne_of_not h2, binomNegOne_of_not h3]
    rw [show (2 * m + 1 + 1 + (2 * n + 1 + 1)) / 2 = m + n + 1 + 1 by omega,
      show (2 * m + 1 + 1) / 2 = m + 1 by omega,
      show (2 * m + 1 + 1 + (2 * n + 1)) / 2 = m + n + 1 by omega,
      show (2 * m + 1 + (2 * n + 1 + 1)) / 2 = m + n + 1 by omega,
      show (2 * m + 1) / 2 = m by omega, Nat.choose_succ_succ,
      show 2 * n + 1 + 1 = 2 * (n + 1) by ring,
      pow_mul]
    push_cast
    ring

/-! ### The closed form of `[a+b, a]` at `q² = −1` -/

section Closed

variable {R : Type*} [CommRing R]

/-- For every specialisation `ψ : ℤ[q, q⁻¹] → R` with `ψ(q²) = −1`,
`ψ [a+b, a] = ψ(q^{-ab}) β(a, b)`. -/
theorem qBinom_eval_of_sq (ψ : A →+* R) (h : ψ (T 2) = -1) (a b : ℕ) :
    ψ (qBinom a b) = ψ (T (-((a * b : ℕ) : ℤ))) * (binomNegOne a b : R) := by
  induction a generalizing b with
  | zero => simp [binomNegOne_zero_left]
  | succ a iha =>
    induction b with
    | zero => simp [binomNegOne_zero_right]
    | succ b ihb =>
      rw [qBinom_succ_succ, map_add, map_mul, map_mul, ihb, iha (b + 1)]
      have e1 : ψ (T (-((a + 1 : ℕ) : ℤ))) * ψ (T (-(((a + 1) * b : ℕ) : ℤ))) =
          ψ (T (-(((a + 1) * (b + 1) : ℕ) : ℤ))) := by
        rw [← map_mul, ← T_add]; congr 2; push_cast; ring
      have e2 : ψ (T ((b + 1 : ℕ) : ℤ)) * ψ (T (-((a * (b + 1) : ℕ) : ℤ))) =
          ψ (T (-(((a + 1) * (b + 1) : ℕ) : ℤ))) * (-1) ^ (b + 1) := by
        rw [← h, ← map_pow, T_pow, ← map_mul, ← map_mul, ← T_add, ← T_add]; congr 2; push_cast; ring
      have hrec := congrArg (Int.cast : ℤ → R) (binomNegOne_rec a b)
      push_cast at hrec
      rw [hrec]
      linear_combination (binomNegOne (a + 1) b : R) * e1 + (binomNegOne a (b + 1) : R) * e2

end Closed

/-- `[a+b, a]` at `q = √−1` is `(−√−1)^{ab} β(a, b)`. -/
theorem evI_qBinom (a b : ℕ) :
    evI (qBinom a b) = (-ii) ^ (a * b) * (binomNegOne a b : GaussianInt) := by
  rw [qBinom_eval_of_sq evI evI_T_two, evI_T_neg_nat]

/-- `[a+b, a]` at `q = −√−1` is `(√−1)^{ab} β(a, b)`. -/
theorem evJ_qBinom' (a b : ℕ) :
    evJ (qBinom a b) = ii ^ (a * b) * (binomNegOne a b : GaussianInt) := by
  rw [qBinom_eval_of_sq evJ evJ_T_two, evJ_T_neg_nat]

/-- **Bar invariance at `q = ±√−1`.** The specialisations of `[a+b, a]` at `q = √−1` and at
`q = −√−1` agree. -/
theorem evJ_qBinom (a b : ℕ) : evJ (qBinom a b) = evI (qBinom a b) := by
  rw [evJ_qBinom', evI_qBinom]
  rcases Nat.even_or_odd (a * b) with h | h
  · rw [neg_pow, h.neg_one_pow, one_mul]
  · have hab := Nat.odd_mul.1 h
    rw [(binomNegOne_eq_zero_iff a b).2 hab]
    simp

/-- **Vanishing of `[a+b, a]` at `q = √−1`** (corrected form of the sentence after (2.1)):
`[a+b, a]_{q=√−1} = 0` iff `a` and `b` are both odd. -/
theorem evI_qBinom_eq_zero_iff (a b : ℕ) : evI (qBinom a b) = 0 ↔ Odd a ∧ Odd b := by
  rw [evI_qBinom, mul_eq_zero, ← binomNegOne_eq_zero_iff, Nat.cast_eq_zero]
  exact or_iff_right (pow_ne_zero _ (neg_ne_zero.2 ii_ne_zero))

/-- `[4, 2]_{q=√−1} = 2`. -/
theorem evI_qBinom_two_two : evI (qBinom 2 2) = 2 := by
  rw [evI_qBinom]
  have : binomNegOne 2 2 = 2 := by decide
  rw [this]
  decide

/-- **The printed sentence after (2.1) is false.** "In particular, it is zero if `a + b` is
even": `[2+2, 2]_{q=√−1} = 2 ≠ 0`. -/
theorem printed_zero_claim_false : ¬ ∀ a b : ℕ, Even (a + b) → evI (qBinom a b) = 0 := by
  intro h
  have := h 2 2 (by decide)
  rw [evI_qBinom_two_two] at this
  exact absurd this (by decide)

/-- `[2, 1]_{q=√−1} = [2]_{q=√−1} = √−1 + (√−1)⁻¹ = 0` (the display at the end of §2.1). -/
theorem evI_qBinom_one_one : evI (qBinom 1 1) = 0 :=
  (evI_qBinom_eq_zero_iff 1 1).2 ⟨odd_one, odd_one⟩

end OddMath.Frontier.EQQuantum
