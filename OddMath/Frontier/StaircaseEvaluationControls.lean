import OddMath.Frontier.StaircaseEvaluation

/-! Controls for EKL arXiv:1111.1320v1, §4.3.1, on the actual carrier: explicit partitions,
their complements `β̂`, and small-rank instances of Lemma 4.9 compared with hand computation
(`D_2 x_1 = 1`; `D_3(x_1 x_3^2) = −1`). -/
namespace OddMath.Frontier.StaircaseEvaluationControls
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open LongestDivided BoxComplement StaircaseEvaluation

/-- `β = (1,0) ∈ P(2,2)` has `β̂ = (2,1)`. -/
theorem hat_example : hat 2 (![1, 0] : Fin 2 → ℕ) = ![2, 1] := by
  funext k; fin_cases k <;> decide

/-- `β = (2) ∈ P(1,2)` has `β̂ = (0,0)`. -/
theorem hat_example' : hat 2 (![2] : Fin 1 → ℕ) = ![0, 0] := by
  funext k; fin_cases k <;> decide

theorem exps_example : exps (![0, 0] : Fin 2 → ℕ) (![2] : Fin 1 → ℕ) = ![1, 0, 2] := by
  funext i; fin_cases i <;> rfl

theorem omega_example : omega (![2] : Fin 1 → ℕ) = 0 := by decide

/-- Lemma 4.9 at `a = 2, b = 1`, `α = 0`, `β = (2)`: `D_3(x_1 x_3^2) = −1`. -/
theorem lemma_4_9_example : D 3 (monomial ![1, 0, 2] 1) = (-1 : ℤ) • 1 := by
  have h := lemma_4_9 (α := (![0, 0] : Fin 2 → ℕ)) (β := (![2] : Fin 1 → ℕ))
    (by intro i j _; fin_cases i <;> fin_cases j <;> decide)
    (by intro k; fin_cases k <;> decide)
    (by intro i j _; fin_cases i; fin_cases j; decide)
    (by intro k; fin_cases k; decide)
  rw [exps_example, hat_example', if_pos rfl, omega_example] at h
  simpa using h

/-- Hand computation in rank two: `D_2 x_1 = ∂_1 x_1 = 1`, matching Lemma 4.9 at `a = b = 1`. -/
theorem rank_two_hand : D 2 (generator 0) = 1 := by
  change AllRankDivided.divided 0 (generator 0) = 1
  rw [AllRankDivided.divided_generator]
  simp

theorem rank_two_lemma : D 2 (monomial ![1, 0] 1) = (1 : ℤ) • 1 := by
  have h := lemma_4_9 (α := (![1] : Fin 1 → ℕ)) (β := (![0] : Fin 1 → ℕ))
    (by intro i j _; fin_cases i; fin_cases j; decide)
    (by intro k; fin_cases k; decide)
    (by intro i j _; fin_cases i; fin_cases j; decide)
    (by intro k; fin_cases k; decide)
  have he : exps (![1] : Fin 1 → ℕ) (![0] : Fin 1 → ℕ) = ![1, 0] := by
    funext i; fin_cases i <;> rfl
  have hh : hat 1 (![0] : Fin 1 → ℕ) = ![1] := by funext k; fin_cases k; decide
  rw [he, hh, if_pos rfl] at h
  simpa using h

end OddMath.Frontier.StaircaseEvaluationControls
