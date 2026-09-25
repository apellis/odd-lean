import OddMath.Frontier.StaircaseEvaluation

/-! Audit for EKL arXiv:1111.1320v1, §4.3.1 (Lemma 4.4 – Lemma 4.9): every headline restated on
the library's `LongestDivided.D` and `AllRankDivided.divided`, with the local definitions
(`hat`, `expA`, `expB`, `omega`, `exps`) unfolded, plus transitive axioms. -/
namespace OddMath.Frontier.StaircaseEvaluationAudit
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open AllRankDivided LongestDivided
open scoped BigOperators

/-- Lemma 4.4, `k = 1`. -/
example (n : ℕ) (i : Fin (n+1)) (m : ℕ) :
    divided i (generator i.castSucc ^ m * generator i.succ ^ (m+1)) =
      (-1 : ℤ)^m • divided i (generator i.castSucc ^ (m+1) * generator i.succ ^ m) :=
  ShuffleLemma.shuffle_one i m

/-- Lemma 4.4, `k` even. -/
example (n : ℕ) (i : Fin (n+1)) (m k : ℕ) (hk : Even k) :
    divided i (generator i.castSucc ^ m * generator i.succ ^ (m+k)) =
      -divided i (generator i.castSucc ^ (m+k) * generator i.succ ^ m) :=
  ShuffleLemma.shuffle_even i m k hk

/-- Lemma 4.4, `k` odd, `k ≥ 3`. -/
example (n : ℕ) (i : Fin (n+1)) (m k : ℕ) (hk : Odd k) (h3 : 3 ≤ k) :
    divided i (generator i.castSucc ^ m * generator i.succ ^ (m+k)) =
      (-1 : ℤ)^m • divided i (generator i.castSucc ^ (m+k) * generator i.succ ^ m) -
      divided i (generator i.castSucc ^ (m+k-1) * generator i.succ ^ (m+1)) +
      (-1 : ℤ)^m • divided i (generator i.castSucc ^ (m+1) * generator i.succ ^ (m+k-1)) :=
  ShuffleLemma.shuffle_odd i m k hk h3

/-- (4.27) as printed is false, in every rank and at every position. -/
example (n : ℕ) (i : Fin (n+1)) :
    ¬ ∀ m k : ℕ, Odd k → 3 ≤ k →
      divided i (generator i.castSucc ^ m * generator i.succ ^ (m+k)) =
        (-1 : ℤ)^m • divided i (generator i.castSucc ^ (m+k) * generator i.succ ^ m) -
        (2 : ℤ) • ∑ j ∈ Finset.Icc 1 (k/2), (-1 : ℤ)^(m*(j+1)) •
          divided i (generator i.castSucc ^ (m+k-j) * generator i.succ ^ (m+j)) :=
  ShuffleLemma.big_shuffle_false i

/-- (4.27) corrected: the sign is `(−1)^{binom(j,2) + (m+1)(j+1)}`. -/
example (n : ℕ) (i : Fin (n+1)) (m k : ℕ) (hk : Odd k) :
    divided i (generator i.castSucc ^ m * generator i.succ ^ (m+k)) =
      (-1 : ℤ)^m • divided i (generator i.castSucc ^ (m+k) * generator i.succ ^ m) -
      (2 : ℤ) • ∑ j ∈ Finset.Icc 1 (k/2), (-1 : ℤ)^(j.choose 2 + (m+1)*(j+1)) •
        divided i (generator i.castSucc ^ (m+k-j) * generator i.succ ^ (m+j)) :=
  ShuffleLemma.big_shuffle i m k hk

/-- Prop 4.5, in rank `m = n+2`. -/
example (n a p : ℕ) (ham : n+2 ≤ a) (hp1 : a-(n+1) ≤ p) (hp2 : p ≤ a-1) :
    D (n+2) (monomial (Fin.snoc (fun i : Fin (n+1) => a-1-i.val) p) 1) = 0 :=
  StaircaseEvaluation.prop_4_5 n a p ham hp1 hp2

/-- Prop 4.6, with `a = m+1`. -/
example (m : ℕ) :
    D (m+1) (monomial (Fin.snoc (fun i : Fin m => m-1-i.val) m) 1) =
        (-1 : ℤ)^(m.choose 3) • D (m+1) (staircase (m+1)) ∧
      D (m+1) (monomial (Fin.snoc (fun i : Fin m => m-1-i.val) m) 1) =
        (-1 : ℤ)^(m.choose 2) • 1 :=
  StaircaseEvaluation.prop_4_6 m

/-- Prop 4.7, every rank. -/
example (N : ℕ) :
    D N (monomial (fun j : Fin N => j.val) 1) = (-1 : ℤ)^(N.choose 4) • D N (staircase N) :=
  MonomialReversal.prop_4_7 N

/-- Lemma 4.9, every `a, b`, with `β̂`, the exponents and `Ω` unfolded. -/
example (a b : ℕ) (α : Fin a → ℕ) (β : Fin b → ℕ)
    (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β) (hβa : ∀ j, β j ≤ a) :
    D (a+b) (monomial (Fin.append (fun k : Fin a => a-1-k.val + α k)
        (fun j : Fin b => j.val + β (Fin.rev j))) 1) =
      (if α = (fun k : Fin a => (Finset.univ.filter (fun j : Fin b => β j ≤ a-1-k.val)).card)
        then (-1 : ℤ)^((∑ j : Fin b, (j.val + β (Fin.rev j)).choose 3) + (a+b).choose 3)
        else 0) • 1 :=
  StaircaseEvaluation.lemma_4_9 hα hαb hβ hβa

/-- Lemma 4.8, every `a, b`. -/
example (a b : ℕ) (α : Fin a → ℕ) (β : Fin b → ℕ)
    (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β) (hβa : ∀ j, β j ≤ a)
    (h : ∑ k, α k + ∑ j, β j ≠ a * b) :
    D (a+b) (monomial (Fin.append (fun k : Fin a => a-1-k.val + α k)
        (fun j : Fin b => j.val + β (Fin.rev j))) 1) = 0 :=
  StaircaseEvaluation.lemma_4_8 hα hαb hβ hβa h

/-- `β̂` is the conjugate of the complement of `β` in the box. -/
example (a b : ℕ) (α : Fin a → ℕ) (β : Fin b → ℕ)
    (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β) (hβa : ∀ j, β j ≤ a) :
    (∀ k j, a-1-k.val + α k ≠ j.val + β (Fin.rev j)) ↔ α = BoxComplement.hat a β :=
  BoxComplement.disjoint_iff_eq_hat hα hαb hβ hβa

/-- Sorting lemma: bounded exponents off the top degree give zero. -/
example (n : ℕ) (γ : Fin (n+2) → ℕ) (hγ : ∀ j, γ j ≤ n+1) (hdeg : ∑ j, γ j ≠ (n+2).choose 2) :
    D (n+2) (monomial γ 1) = 0 :=
  StaircaseSorting.D_monomial_eq_zero_of_bounded γ hγ hdeg

#print axioms ShuffleLemma.shuffle_one
#print axioms ShuffleLemma.shuffle_even
#print axioms ShuffleLemma.shuffle_odd
#print axioms ShuffleLemma.big_shuffle_false
#print axioms ShuffleLemma.big_shuffle
#print axioms StaircaseEvaluation.prop_4_5
#print axioms StaircaseEvaluation.prop_4_6
#print axioms MonomialReversal.prop_4_7
#print axioms StaircaseEvaluation.lemma_4_8
#print axioms StaircaseEvaluation.lemma_4_9
#print axioms StaircaseValley.top_valley
#print axioms StaircaseSorting.D_monomial_eq_zero_of_bounded

end OddMath.Frontier.StaircaseEvaluationAudit
