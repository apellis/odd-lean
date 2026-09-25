import OddMath.Frontier.LongestElementary
import OddMath.Frontier.LongestReversal

/-!
# Signed permutations acting on skew monomials

EKL arXiv:1111.1320v1 §2.2, (2.2): `σ` acts by `x_j ↦ sgn(σ) x_{σ j}`.  A monomial
is the increasing-index ordered product of generator powers; transporting it by `σ`
and re-sorting gives `sgn(σ)^{|γ|} (-1)^{Σ γ_i γ_j}` (over pairs `i < j` inverted
by `σ`) times the permuted monomial.  For the order reversal `w₀` every pair is
inverted, which is the monomial sign underlying Corollary 2.23.  Combined with the
reversed-staircase normalization this gives Proposition 4.7:
`D_N(x^{(0,1,…,N-1)}) = (-1)^{C(N,3)+C(N,4)}`.
-/

namespace OddMath.Frontier.MonomialReversal

open OddMath.SkewPolynomial
open SignedPermutation LongestElementary
open scoped BigOperators

variable {n : ℕ}

theorem monomial_mul_monomial (a b : Fin n → ℕ) (r s : ℤ) :
    monomial a r * monomial b s = monomial (a + b) (r * s * OddMath.skewSign a b) :=
  mul_monomial a b r s

theorem crossingCount_sum_right {ι : Type*} (a : Fin n → ℕ) (b : ι → Fin n → ℕ)
    (s : Finset ι) :
    OddMath.crossingCount a (∑ q ∈ s, b q) = ∑ q ∈ s, OddMath.crossingCount a (b q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [crossingCount_zero_right]
  | @insert x s h ih => rw [Finset.sum_insert h, Finset.sum_insert h,
      OddMath.crossingCount_add_right, ih]

theorem crossingCount_smul_left (k : ℕ) (a b : Fin n → ℕ) :
    OddMath.crossingCount (k • a) b = k * OddMath.crossingCount a b := by
  simp only [OddMath.crossingCount, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem crossingCount_smul_right (k : ℕ) (a b : Fin n → ℕ) :
    OddMath.crossingCount a (k • b) = k * OddMath.crossingCount a b := by
  simp only [OddMath.crossingCount, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem crossingCount_power (k l : ℕ) (i j : Fin n) :
    OddMath.crossingCount (k • expSingle i) (l • expSingle j) =
      if j < i then k * l else 0 := by
  rw [crossingCount_smul_left, crossingCount_smul_right, crossingCount_expSingle]
  split_ifs <;> ring

/-- Ordered products of monomials: exponents add, coefficients multiply, and every
ordered pair of factors contributes its crossing count. -/
theorem prod_ofFn_monomial : ∀ {N : ℕ} (f : Fin N → Fin n → ℕ) (c : Fin N → ℤ),
    (List.ofFn fun p => monomial (f p) (c p)).prod =
      monomial (∑ p, f p) ((∏ p, c p) * (-1 : ℤ) ^
        ∑ p, ∑ q, if p < q then OddMath.crossingCount (f p) (f q) else 0)
  | 0, _, _ => by simp; rfl
  | N+1, f, c => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_monomial, monomial_mul_monomial,
      Fin.sum_univ_succ (f := f)]
    congr 1
    simp only [Fin.sum_univ_succ, Fin.prod_univ_succ, lt_irrefl, Fin.succ_pos,
      Fin.succ_lt_succ_iff, Fin.not_lt_zero, if_true, if_false, zero_add,
      OddMath.skewSign, crossingCount_sum_right, pow_add]
    ring

/-- The unit monomial is the increasing-index ordered product of generator powers. -/
theorem monomial_eq_prod (γ : Fin n → ℕ) :
    monomial γ 1 = (List.ofFn fun j => generator j ^ γ j).prod := by
  simp_rw [PbwL4.pow_form]
  rw [prod_ofFn_monomial]
  congr 1
  · funext t
    simp [Finset.sum_apply, expSingle]
  · simp only [crossingCount_power, Finset.prod_const_one, _root_.one_mul]
    rw [Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_, pow_zero]
    split_ifs with h h' <;> first | rfl | exact absurd h' (not_lt_of_gt h)

theorem monomial_eq_smul_prod (γ : Fin n → ℕ) (c : ℤ) :
    monomial γ c = c • (List.ofFn fun j => generator j ^ γ j).prod := by
  rw [PbwL4.monomial_smul, monomial_eq_prod]

/-- EKL (2.2) on an arbitrary monomial: the sign is `sgn(σ)^{|γ|}` times one factor
`(-1)^{γ_i γ_j}` for each pair `i < j` inverted by `σ`. -/
theorem action_monomial (σ : Equiv.Perm (Fin n)) (γ : Fin n → ℕ) (c : ℤ) :
    skewAction σ (monomial γ c) =
      (epsilon σ ^ (∑ j, γ j) * (-1 : ℤ) ^
        (∑ i, ∑ j, if i < j ∧ σ j < σ i then γ i * γ j else 0)) •
        monomial (fun t => γ (σ.symm t)) c := by
  rw [monomial_eq_smul_prod, map_zsmul, map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, map_pow, action_generator, smul_pow]
  simp only [PbwL4.pow_form]
  simp_rw [← PbwL4.monomial_smul]
  rw [prod_ofFn_monomial, Finset.prod_pow_eq_pow_sum]
  have he : (∑ p, γ p • expSingle (σ p)) = fun t => γ (σ.symm t) := by
    funext t
    simp [Finset.sum_apply, expSingle, Equiv.apply_eq_iff_eq_symm_apply]
  simp only [he, crossingCount_power, ite_and, Finsupp.smul_single, smul_eq_mul]
  rw [mul_comm c]

/-- Order reversal on a monomial: `x_j ↦ (-1)^{C(N,2)} x_{N-1-j}` and re-sorting
the reversed word costs one sign `(-1)^{γ_i γ_j}` for every pair `i < j`. -/
theorem longest_monomial (N : ℕ) (γ : Fin N → ℕ) (c : ℤ) :
    SignedPermutation.skewAction (LongestElementary.longest N) (monomial γ c) =
      ((-1 : ℤ) ^ (N.choose 2 * ∑ j, γ j + ∑ i, ∑ j, if i < j then γ i * γ j else 0)) •
        monomial (fun j => γ (Fin.rev j)) c := by
  rw [action_monomial, epsilon_longest, ← pow_mul, ← pow_add]
  simp only [longest_apply, Fin.rev_lt_rev, and_self]
  rfl

theorem sum_rev_val : ∀ N : ℕ, ∑ j : Fin N, (N - 1 - j.val) = N.choose 2
  | 0 => rfl
  | N+1 => by
    rw [Fin.sum_univ_succ, Finset.sum_congr rfl
      (fun j _ => show N + 1 - 1 - (Fin.succ j).val = N - 1 - j.val by
        simp only [Fin.val_succ]; omega), sum_rev_val N, Nat.choose_succ_succ' N 1,
      Nat.choose_one_right]
    simp

theorem mul_choose_two (N : ℕ) : N * N.choose 2 = N.choose 3 + 2 * (N+1).choose 3 := by
  have h1 := Nat.succ_mul_choose_eq N 2
  have h2 := Nat.choose_succ_succ' N 2
  linarith

theorem even_pairSum_add_choose_four : ∀ N : ℕ,
    Even ((∑ i : Fin N, ∑ j : Fin N,
      if i < j then (N - 1 - i.val) * (N - 1 - j.val) else 0) + N.choose 4)
  | 0 => by simp
  | N+1 => by
    obtain ⟨k, hk⟩ := even_pairSum_add_choose_four N
    have hs : (∑ i : Fin (N+1), ∑ j : Fin (N+1),
        if i < j then (N + 1 - 1 - i.val) * (N + 1 - 1 - j.val) else 0) =
        N * N.choose 2 + ∑ i : Fin N, ∑ j : Fin N,
          if i < j then (N - 1 - i.val) * (N - 1 - j.val) else 0 := by
      simp only [Fin.sum_univ_succ, lt_irrefl, Fin.succ_pos, Fin.succ_lt_succ_iff,
        Fin.not_lt_zero, if_true, if_false, zero_add, Fin.val_zero, Fin.val_succ]
      rw [← sum_rev_val N, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by congr 1; omega
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs
        · congr 1 <;> omega
        · rfl
    have hc := Nat.choose_succ_succ' N 3
    have hm := mul_choose_two N
    refine ⟨k + N.choose 3 + (N+1).choose 3, ?_⟩
    rw [hs, hc]
    linarith

theorem neg_one_pow_of_even_add {a b : ℕ} (h : Even (a + b)) :
    (-1 : ℤ) ^ a = (-1 : ℤ) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two (R := ℤ), neg_one_pow_eq_pow_mod_two (R := ℤ) (n := b)]
  rw [Nat.even_iff] at h
  congr 1
  omega

/-- EKL Proposition 4.7, evaluated: the divided difference of the increasing
staircase `x^{(0,1,…,N-1)}`. -/
theorem D_increasing_staircase (N : ℕ) :
    LongestDivided.D N (monomial (fun j : Fin N => j.val) 1) =
      (-1 : ℤ) ^ (N.choose 3 + N.choose 4) • (1 : SkewPolynomial N) := by
  have h := LongestReversal.D_reversed_staircase N
  have hm : (fun j : Fin N => N - 1 - (Fin.rev j).val) = fun j => j.val := by
    funext j
    simp only [Fin.val_rev]
    omega
  rw [LongestDivided.staircase, longest_monomial, map_zsmul, sum_rev_val, hm] at h
  set E := N.choose 2 * N.choose 2 + ∑ i : Fin N, ∑ j : Fin N,
    if i < j then (N - 1 - i.val) * (N - 1 - j.val) else 0
  have hE : Even (E + (N+1).choose 3 + (N.choose 3 + N.choose 4)) := by
    obtain ⟨k, hk⟩ := even_pairSum_add_choose_four N
    obtain ⟨l, hl⟩ := Nat.even_mul_succ_self (N.choose 2)
    have hc := Nat.choose_succ_succ' N 2
    refine ⟨k + l + N.choose 3, ?_⟩
    simp only [E]
    rw [hc]
    nlinarith
  calc LongestDivided.D N (monomial (fun j : Fin N => j.val) 1)
      = ((-1 : ℤ) ^ E * (-1 : ℤ) ^ E) •
          LongestDivided.D N (monomial (fun j : Fin N => j.val) 1) := by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
    _ = (-1 : ℤ) ^ (E + (N+1).choose 3) • (1 : SkewPolynomial N) := by
        rw [mul_smul, h, smul_smul, ← pow_add]
    _ = _ := by rw [neg_one_pow_of_even_add hE]

/-- EKL Proposition 4.7, literal form. -/
theorem prop_4_7 (N : ℕ) :
    LongestDivided.D N (monomial (fun j : Fin N => j.val) 1) =
      (-1 : ℤ) ^ (N.choose 4) • LongestDivided.D N (LongestDivided.staircase N) := by
  rw [D_increasing_staircase, LongestDivided.D_staircase, smul_smul, ← pow_add, add_comm]

end OddMath.Frontier.MonomialReversal
