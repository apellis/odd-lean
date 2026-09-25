import OddMath.Frontier.ShuffleLemma
import OddMath.Frontier.LongestFactor

/-! # Sorting exponents under the longest odd divided difference

EKL arXiv:1111.1320v1, §4.3.1, pp. 35–36.  Using the Shuffle Lemma 4.4 an ascent in the
exponent vector is rewritten through descents whose entries stay in the same range, and
equal adjacent exponents are killed.  Consequently `D_N(x^γ) = 0` whenever every exponent is
at most `N − 1` and `|γ| ≠ binom(N,2)`, and whenever every exponent is at most `N − 2`.
This is the vanishing mechanism behind Lemma 4.8. -/
namespace OddMath.Frontier.StaircaseSorting
open OddMath.SkewPolynomial (SkewPolynomial monomial)
open scoped BigOperators

variable {n : ℕ}

/-- Weight favouring large exponents on the left; rewriting an ascent increases it. -/
def weight (γ : Fin (n+2) → ℕ) : ℕ := ∑ j : Fin (n+2), (n+1-j.val) * γ j

theorem weight_le (γ : Fin (n+2) → ℕ) : weight γ ≤ (n+1) * ∑ j, γ j := by
  rw [weight, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (Nat.sub_le _ _)

/-- Changing an ascent into a descent of the same total raises the weight. -/
theorem weight_lt_of_swap (i : Fin (n+1)) (γ γ' : Fin (n+2) → ℕ)
    (hoff : ∀ j, j ≠ i.castSucc → j ≠ i.succ → γ' j = γ j)
    (hasc : γ i.castSucc < γ i.succ) (hdesc : γ' i.succ < γ' i.castSucc)
    (hsum : γ' i.castSucc + γ' i.succ = γ i.castSucc + γ i.succ) :
    weight γ < weight γ' := by
  have hne : i.castSucc ≠ i.succ := AllRankDivided.adjacent_ne i
  have split : ∀ δ : Fin (n+2) → ℕ, weight δ =
      (∑ j ∈ (Finset.univ.erase i.castSucc).erase i.succ, (n+1-j.val) * δ j) +
        (n+1-i.val) * δ i.castSucc + (n-i.val) * δ i.succ := by
    intro δ
    rw [weight, ← Finset.add_sum_erase _ _ (Finset.mem_univ i.castSucc),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ i.succ⟩)]
    simp only [Fin.coe_castSucc, Fin.val_succ]
    have : n+1-(i.val+1) = n-i.val := by omega
    rw [this]; ring
  have hrest : (∑ j ∈ (Finset.univ.erase i.castSucc).erase i.succ, (n+1-j.val) * γ' j) =
      ∑ j ∈ (Finset.univ.erase i.castSucc).erase i.succ, (n+1-j.val) * γ j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hj
    rw [hoff j (Finset.ne_of_mem_erase h2) h1]
  rw [split γ, split γ', hrest]
  have hi : i.val < n+1 := i.isLt
  -- the pair contributes (n-i)*(p+q) + p, where p is the left exponent
  have key : ∀ p q : ℕ, (n+1-i.val) * p + (n-i.val) * q = (n-i.val) * (p+q) + p := by
    intro p q
    have : n+1-i.val = (n-i.val) + 1 := by omega
    rw [this]; ring
  have k1 := key (γ i.castSucc) (γ i.succ)
  have k2 := key (γ' i.castSucc) (γ' i.succ)
  rw [hsum] at k2
  omega

/-- The core sorting argument, for an arbitrary exponent bound. -/
theorem D_monomial_eq_zero_of_no_strict (Bd : ℕ) (γ : Fin (n+2) → ℕ) (hγ : ∀ j, γ j ≤ Bd)
    (hno : ∀ δ : Fin (n+2) → ℕ, (∀ j, δ j ≤ Bd) → (∑ j, δ j) = ∑ j, γ j → ¬ StrictAnti δ) :
    LongestDivided.D (n+2) (monomial γ 1) = 0 := by
  -- strong induction on the distance of the weight to its maximum
  suffices H : ∀ t : ℕ, ∀ γ : Fin (n+2) → ℕ, (∀ j, γ j ≤ Bd) →
      (∀ δ : Fin (n+2) → ℕ, (∀ j, δ j ≤ Bd) → (∑ j, δ j) = ∑ j, γ j → ¬ StrictAnti δ) →
      (n+1) * (∑ j, γ j) - weight γ = t → LongestDivided.D (n+2) (monomial γ 1) = 0 from
    H _ γ hγ hno rfl
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro γ hγ hno ht
  by_cases hsd : StrictAnti γ
  · exact absurd hsd (hno γ hγ rfl)
  -- not strictly decreasing: find a non-descent at some adjacent pair
  have : ∃ i : Fin (n+1), γ i.castSucc ≤ γ i.succ := by
    by_contra hcon
    push_neg at hcon
    apply hsd
    exact Fin.strictAnti_iff_succ_lt.mpr fun i => hcon i
  obtain ⟨i, hi⟩ := this
  obtain ⟨L, ε, -, hD⟩ := LongestFactor.D_factor_first n i
  rcases hi.lt_or_eq with hlt | heq
  · have hmem := ShuffleLemma.divided_monomial_ascent_mem_span i γ hlt
    have hzero : ∀ x ∈ Submodule.span ℤ
        ((fun γ' => AllRankDivided.divided i (monomial γ' 1)) ''
          {γ' | (∀ j, j ≠ i.castSucc → j ≠ i.succ → γ' j = γ j) ∧
              γ' i.succ < γ' i.castSucc ∧ γ i.castSucc ≤ γ' i.succ ∧ γ' i.castSucc ≤ γ i.succ ∧
              γ' i.castSucc + γ' i.succ = γ i.castSucc + γ i.succ}),
        ε • L x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨γ', ⟨hoff, hdesc, hlo, hhi, hsum⟩, rfl⟩ := hx
          have hsumγ : ∑ j, γ' j = ∑ j, γ j := by
            have hne : i.castSucc ≠ i.succ := AllRankDivided.adjacent_ne i
            have hs : ∀ δ : Fin (n+2) → ℕ, ∑ j, δ j =
                (∑ j ∈ (Finset.univ.erase i.castSucc).erase i.succ, δ j) +
                  (δ i.castSucc + δ i.succ) := by
              intro δ
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i.castSucc),
                ← Finset.add_sum_erase _ _
                  (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ i.succ⟩)]
              ring
            rw [hs γ', hs γ, hsum]
            congr 1
            refine Finset.sum_congr rfl fun j hj => ?_
            obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hj
            exact hoff j (Finset.ne_of_mem_erase h2) h1
          have hbd : ∀ j, γ' j ≤ Bd := by
            intro j
            by_cases h1 : j = i.castSucc
            · subst h1; exact le_trans hhi (hγ _)
            by_cases h2 : j = i.succ
            · subst h2; exact le_trans (le_of_lt (lt_of_lt_of_le hdesc hhi)) (hγ _)
            rw [hoff j h1 h2]; exact hγ j
          have hw := weight_lt_of_swap i γ γ' hoff hlt hdesc hsum
          have hwle := weight_le γ'
          rw [hsumγ] at hwle
          have hIH := ih ((n+1) * (∑ j, γ' j) - weight γ') (by rw [← ht, hsumγ]; omega)
            γ' hbd (by rw [hsumγ]; exact hno) rfl
          rw [hD] at hIH
          simpa using hIH
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, smul_add, hx, hy, add_zero]
      | smul r x _ hx => rw [map_zsmul, smul_comm, hx, smul_zero]
    rw [hD]
    simpa using hzero _ hmem
  · rw [hD]
    simp [ShuffleLemma.divided_monomial_balanced i γ 1 heq]

/-- The only strictly decreasing exponent vector with entries `≤ N−1` is the staircase. -/
theorem strictAnti_bounded_eq (δ : Fin (n+2) → ℕ) (hδ : ∀ j, δ j ≤ n+1) (hs : StrictAnti δ) :
    ∀ j, δ j = n+1-j.val := by
  have lower : ∀ k : ℕ, ∀ j : Fin (n+2), n+1-j.val = k → k ≤ δ j := by
    intro k
    induction k with
    | zero => intro j _; exact Nat.zero_le _
    | succ k ih =>
        intro j hj
        have hjl : j.val + 1 < n+2 := by omega
        have := ih ⟨j.val+1, hjl⟩ (by simp; omega)
        have hlt := hs (show j < ⟨j.val+1, hjl⟩ from Fin.mk_lt_mk.mpr (by omega))
        omega
  have upper : ∀ j : Fin (n+2), δ j ≤ n+1-j.val := by
    intro j
    induction j using Fin.induction with
    | zero => simpa using hδ 0
    | succ j ih =>
        have := hs (Fin.castSucc_lt_succ j)
        simp only [Fin.coe_castSucc] at ih
        simp only [Fin.val_succ]
        omega
  intro j
  exact le_antisymm (upper j) (lower _ j rfl)

theorem sum_staircase_exp (n : ℕ) : ∑ j : Fin (n+2), (n+1-j.val) = (n+2).choose 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => n+1-j) (n+2)]
  have h := Finset.sum_range_reflect (fun j => j) (n+2)
  simp only [show n+2-1 = n+1 by omega] at h
  rw [h, Finset.sum_range_id, Nat.choose_two_right]

/-- Sorting lemma: bounded exponents off the top degree give zero. -/
theorem D_monomial_eq_zero_of_bounded (γ : Fin (n+2) → ℕ) (hγ : ∀ j, γ j ≤ n+1)
    (hdeg : ∑ j, γ j ≠ (n+2).choose 2) : LongestDivided.D (n+2) (monomial γ 1) = 0 := by
  refine D_monomial_eq_zero_of_no_strict (n+1) γ hγ fun δ hδ hsum hs => hdeg ?_
  rw [← hsum, Finset.sum_congr rfl fun j _ => strictAnti_bounded_eq δ hδ hs j]
  exact sum_staircase_exp n

/-- Exponents all at most `N − 2` give zero in every degree. -/
theorem D_monomial_eq_zero_of_small (γ : Fin (n+2) → ℕ) (hγ : ∀ j, γ j ≤ n) :
    LongestDivided.D (n+2) (monomial γ 1) = 0 := by
  refine D_monomial_eq_zero_of_no_strict n γ hγ fun δ hδ _ hs => ?_
  have := strictAnti_bounded_eq δ (fun j => le_trans (hδ j) (Nat.le_succ n)) hs 0
  have h0 := hδ 0
  simp at this
  omega

end OddMath.Frontier.StaircaseSorting
