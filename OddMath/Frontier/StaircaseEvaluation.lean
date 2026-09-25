import OddMath.Frontier.StaircaseValley

/-! # EKL §4.3.1: evaluations of `D_a` on staircase-type monomials

EKL arXiv:1111.1320v1, §4.3.1, Props 4.5–4.7 and Lemmas 4.8–4.9, pp. 35–37, in every rank.

For `α ∈ P(a,b)` and `β ∈ P(b,a)` the monomial of (4.32)–(4.33) has exponents
`a−1+α_1 > ⋯ > α_a` on the first `a` variables and `β_b < 1+β_{b−1} < ⋯ < b−1+β_1` on the
last `b` variables (`BoxComplement.expA`, `BoxComplement.expB`).  Lemma 4.9:
`D_{a+b}(x^{…}) = δ_{α,β̂} (−1)^{Ω(β) + binom(a+b,3)}` with `Ω(β) = Σ_j binom(β_{b−j}+j, 3)`.

The printed proofs of Lemmas 4.8–4.9 argue by shuffling exponents; here Lemma 4.8 follows from
the sorting lemma (`StaircaseSorting`) and Lemma 4.9 from the valley theorem
(`StaircaseValley.top_valley`), whose sign exponent `Σ_{v ∈ B} binom(v,3)` is `Ω(β)`.
Prop 4.7 is `MonomialReversal.prop_4_7`. -/
namespace OddMath.Frontier.StaircaseEvaluation
open OddMath.SkewPolynomial (SkewPolynomial monomial)
open LongestDivided BoxComplement StaircaseValley
open scoped BigOperators

/-! ## Lemmas 4.8 and 4.9 -/

/-- EKL (4.34): `Ω(β) = Σ_{j=0}^{b−1} binom(β_{b−j} + j, 3)`. -/
def omega {b : ℕ} (β : Fin b → ℕ) : ℕ := ∑ j : Fin b, (j.val + β (Fin.rev j)).choose 3

/-- The exponent vector of EKL (4.32)–(4.33). -/
def exps {a b : ℕ} (α : Fin a → ℕ) (β : Fin b → ℕ) : Fin (a+b) → ℕ :=
  Fin.append (expA α) (expB β)

theorem exps_left {a b : ℕ} (α : Fin a → ℕ) (β : Fin b → ℕ) (i : Fin (a+b)) (h : i.val < a) :
    exps α β i = expA α ⟨i.val, h⟩ :=
  (congrArg (exps α β) (Fin.ext rfl : i = Fin.castAdd b ⟨i.val, h⟩)).trans
    (Fin.append_left _ _ _)

theorem exps_right {a b : ℕ} (α : Fin a → ℕ) (β : Fin b → ℕ) (i : Fin (a+b)) (h : a ≤ i.val) :
    exps α β i = expB β ⟨i.val - a, by omega⟩ :=
  (congrArg (exps α β)
      (Fin.ext (by simp; omega) : i = Fin.natAdd a ⟨i.val - a, by omega⟩)).trans
    (Fin.append_right _ _ _)

theorem sum_exps {a b : ℕ} (α : Fin a → ℕ) (β : Fin b → ℕ) :
    ∑ i, exps α β i + a * b = (a+b).choose 2 + ∑ k, α k + ∑ j, β j := by
  rw [exps, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  exact sum_expA_add_sum_expB

theorem exps_isValley {a b : ℕ} {α : Fin a → ℕ} {β : Fin b → ℕ} (hα : Antitone α)
    (hβ : Antitone β) : IsValley (exps α β) a := by
  refine ⟨fun i j hij hj => ?_, fun i j hij hi => ?_⟩
  · rw [exps_left α β i (by have := Fin.lt_def.mp hij; omega), exps_left α β j hj]
    exact expA_strictAnti hα (Fin.mk_lt_mk.mpr (Fin.lt_def.mp hij))
  · rw [exps_right α β i hi, exps_right α β j (by have := Fin.lt_def.mp hij; omega)]
    exact expB_strictMono hβ (Fin.mk_lt_mk.mpr (by have := Fin.lt_def.mp hij; omega))

theorem exps_injective_iff {a b : ℕ} {α : Fin a → ℕ} {β : Fin b → ℕ} (hα : Antitone α)
    (hβ : Antitone β) :
    Function.Injective (exps α β) ↔ ∀ k j, expA α k ≠ expB β j := by
  constructor
  · intro h k j hkj
    have := h (show exps α β (Fin.castAdd b k) = exps α β (Fin.natAdd a j) by
      rw [exps, Fin.append_left, Fin.append_right, hkj])
    have := congrArg Fin.val this
    simp at this
    omega
  · intro h i i' hii
    rcases Nat.lt_or_ge i.val a with hi | hi <;> rcases Nat.lt_or_ge i'.val a with hi' | hi'
    · rw [exps_left α β i hi, exps_left α β i' hi'] at hii
      exact Fin.ext (by simpa using (expA_strictAnti hα).injective hii)
    · rw [exps_left α β i hi, exps_right α β i' hi'] at hii
      exact absurd hii (h _ _)
    · rw [exps_right α β i hi, exps_left α β i' hi'] at hii
      exact absurd hii.symm (h _ _)
    · rw [exps_right α β i hi, exps_right α β i' hi'] at hii
      have := (expB_strictMono hβ).injective hii
      simp at this
      exact Fin.ext (by omega)

theorem armSum_exps {a b : ℕ} (α : Fin a → ℕ) (β : Fin b → ℕ) :
    armSum (exps α β) a = omega β := by
  rw [armSum, exps, Fin.sum_univ_add, omega]
  simp only [Fin.coe_castAdd, Fin.coe_natAdd, Fin.append_right]
  rw [Finset.sum_eq_zero fun i _ => if_neg (by omega), zero_add]
  exact Finset.sum_congr rfl fun j _ => by rw [if_pos (by omega)]; rfl

theorem exps_lt {a b : ℕ} {α : Fin a → ℕ} {β : Fin b → ℕ} (hαb : ∀ k, α k ≤ b)
    (hβa : ∀ j, β j ≤ a) (i : Fin (a+b)) : exps α β i < a + b := by
  rcases Nat.lt_or_ge i.val a with hi | hi
  · rw [exps_left α β i hi]; exact expA_lt hαb _
  · rw [exps_right α β i hi]; exact expB_lt hβa _

/-- EKL Lemma 4.9 (all `a, b`, including Lemma 4.8). -/
theorem lemma_4_9 {a b : ℕ} {α : Fin a → ℕ} {β : Fin b → ℕ}
    (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β) (hβa : ∀ j, β j ≤ a) :
    D (a+b) (monomial (exps α β) 1) =
      (if α = hat a β then (-1 : ℤ)^(omega β + (a+b).choose 3) else 0) • 1 := by
  have hsum := sum_exps α β
  by_cases hdeg : ∑ i, exps α β i = (a+b).choose 2
  · rw [D_eq_top hdeg, top_valley _ _ a (exps_isValley hα hβ) hdeg,
      armSum_exps, add_comm ((a+b).choose 3)]
    congr 1
    exact if_congr ((exps_injective_iff hα hβ).trans (disjoint_iff_eq_hat hα hαb hβ hβa))
      rfl rfl
  · have hne : α ≠ hat a β := by
      rintro rfl
      have := sum_hat (a := a) hβa
      omega
    rw [if_neg hne, zero_smul]
    -- off the top degree every exponent is `≤ a+b−1`, so the sorting lemma applies
    rcases Nat.lt_or_ge (a+b) 2 with hsmall | hbig
    · exfalso
      apply hdeg
      have : ∀ i, exps α β i = 0 := fun i => by have := exps_lt hαb hβa i; omega
      simp only [this, Finset.sum_const_zero]
      rcases (show a+b = 0 ∨ a+b = 1 by omega) with h | h <;> rw [h] <;> rfl
    · obtain ⟨n, hn⟩ : ∃ n, a+b = n+2 := ⟨a+b-2, by omega⟩
      have key : ∀ (N : ℕ) (hN : N = n+2) (γ : Fin N → ℕ), (∀ i, γ i ≤ n+1) →
          ∑ i, γ i ≠ N.choose 2 → D N (monomial γ 1) = 0 := by
        rintro N rfl γ hγ hd
        exact StaircaseSorting.D_monomial_eq_zero_of_bounded γ hγ hd
      exact key (a+b) hn _ (fun i => by have := exps_lt hαb hβa i; omega) hdeg

/-- EKL Lemma 4.8: the evaluation vanishes unless `|α| + |β| = ab`. -/
theorem lemma_4_8 {a b : ℕ} {α : Fin a → ℕ} {β : Fin b → ℕ}
    (hα : Antitone α) (hαb : ∀ k, α k ≤ b) (hβ : Antitone β) (hβa : ∀ j, β j ≤ a)
    (h : ∑ k, α k + ∑ j, β j ≠ a * b) : D (a+b) (monomial (exps α β) 1) = 0 := by
  rw [lemma_4_9 hα hαb hβ hβa, if_neg, zero_smul]
  rintro rfl
  exact h (sum_hat hβa)

/-! ## Props 4.5 and 4.6 -/

/-- EKL Prop 4.6: `D_a(x_1^{a−2} ⋯ x_{a−1}^0 x_a^{a−1}) = (−1)^{binom(a−1,3)} D_a(x^{δ_a})
= (−1)^{binom(a−1,2)}`, written with `a = m+1`. -/
theorem prop_4_6 (m : ℕ) :
    D (m+1) (monomial (Fin.snoc (fun i : Fin m => m-1-i.val) m) 1) =
        (-1 : ℤ)^(m.choose 3) • D (m+1) (staircase (m+1)) ∧
      D (m+1) (monomial (Fin.snoc (fun i : Fin m => m-1-i.val) m) 1) =
        (-1 : ℤ)^(m.choose 2) • 1 := by
  have hval : D (m+1) (monomial (Fin.snoc (fun i : Fin m => m-1-i.val) m) 1) =
      (-1 : ℤ)^(m.choose 2) • 1 := by
    rcases m with _ | _ | n
    · change monomial _ 1 = _
      simp
      rfl
    · have : (Fin.snoc (fun i : Fin 1 => 1-1-i.val) 1 : Fin 2 → ℕ) = fun i => i.val := by
        funext i; fin_cases i <;> rfl
      rw [this, MonomialReversal.D_increasing_staircase]
      rfl
    · have hs : ∑ i : Fin (n+2), (n+2-1-i.val) = (n+2).choose 2 := sum_staircase (n+2)
      have hs' : ∑ i, (Fin.snoc (fun i : Fin (n+2) => n+2-1-i.val) (n+2) : Fin (n+3) → ℕ) i =
          (n+3).choose 2 := by
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [hs, Nat.choose_succ_succ' (n+2) 1, Nat.choose_one_right]
        ring
      rw [D_eq_top hs', right_peel n _ hs, top_staircase]
      have e : (n+3).choose 3 = (n+2).choose 2 + (n+2).choose 3 := Nat.choose_succ_succ' _ _
      rw [e, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
  refine ⟨?_, hval⟩
  rw [hval, D_staircase, smul_smul, ← pow_add]
  congr 1
  rcases m with _ | m
  · rfl
  · have e : (m+1+1).choose 3 = (m+1).choose 2 + (m+1).choose 3 := Nat.choose_succ_succ' _ _
    rw [e, add_comm ((m+1).choose 2), ← add_assoc, pow_add, ← two_mul, pow_mul]
    norm_num

/-- A monomial with all exponents equal lies in the odd symmetric polynomials. -/
theorem const_monomial_mem (n c : ℕ) :
    monomial (fun _ : Fin (n+2) => c) 1 ∈ OddSymmetricKernel.kernelSubring n := by
  rw [OddSymmetricKernel.mem_kernelSubring]
  intro i
  exact ShuffleLemma.divided_monomial_balanced i _ 1 rfl

/-- EKL Prop 4.5: for `a ≥ m ≥ 2` and `a−(m−1) ≤ p ≤ a−1`,
`D_m(x_1^{a−1} x_2^{a−2} ⋯ x_{m−1}^{a−(m−1)} x_m^p) = 0`, written with `m = n+2`. -/
theorem prop_4_5 (n a p : ℕ) (ham : n+2 ≤ a) (hp1 : a-(n+1) ≤ p) (hp2 : p ≤ a-1) :
    D (n+2) (monomial (Fin.snoc (fun i : Fin (n+1) => a-1-i.val) p) 1) = 0 := by
  set c := a-(n+1)
  set η' : Fin (n+2) → ℕ := Fin.snoc (fun i : Fin (n+1) => n-i.val) (p-c)
  have hsplit : (Fin.snoc (fun i : Fin (n+1) => a-1-i.val) p : Fin (n+2) → ℕ) =
      η' + fun _ => c := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.snoc_last, Pi.add_apply, η']; omega
    · simp only [Fin.snoc_castSucc, Pi.add_apply, η']; have := i.isLt; omega
  have hsmall : ∀ i, η' i ≤ n := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.snoc_last, η']; omega
    · simp only [Fin.snoc_castSucc, η']; omega
  have hmul := MonomialReversal.monomial_mul_monomial η' (fun _ => c) 1 1
  rw [← hsplit, one_mul, one_mul] at hmul
  have hsign : OddMath.skewSign η' (fun _ => c) * OddMath.skewSign η' (fun _ => c) = 1 := by
    rw [OddMath.skewSign, ← mul_pow]; simp
  have hmono : monomial (Fin.snoc (fun i : Fin (n+1) => a-1-i.val) p) (1 : ℤ) =
      OddMath.skewSign η' (fun _ => c) •
        (monomial η' 1 * monomial (fun _ : Fin (n+2) => c) 1) := by
    rw [hmul]
    rw [show (OddMath.skewSign η' (fun _ => c)) •
        monomial (Fin.snoc (fun i : Fin (n+1) => a-1-i.val) p) (OddMath.skewSign η' fun _ => c) =
        monomial (Fin.snoc (fun i : Fin (n+1) => a-1-i.val) p)
          (OddMath.skewSign η' (fun _ => c) * OddMath.skewSign η' (fun _ => c)) by
      simp [OddMath.SkewPolynomial.monomial]]
    rw [hsign]
  rw [hmono, map_zsmul, D_right_kernel n _ _ (const_monomial_mem n c),
    StaircaseSorting.D_monomial_eq_zero_of_small η' hsmall]
  rw [show (0 : SkewPolynomial (n+2)) * monomial (fun _ : Fin (n+2) => c) 1 = 0 from
    OddMath.SkewPolynomial.zero_mul _, smul_zero]

end OddMath.Frontier.StaircaseEvaluation
