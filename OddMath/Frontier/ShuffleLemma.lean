import OddMath.Frontier.LongestDivided
import Mathlib.Algebra.BigOperators.Intervals

/-! # The shuffle lemma
EKL arXiv:1111.1320v1, §4.3.1, Lemma 4.4, p. 35.

Write `P(p,q) = ∂_i(x_i^p x_{i+1}^q)`.  The kernel of `∂_i` is closed under products and
contains `x_i - x_{i+1}` and `x_i^2 x_{i+1}^2`; hence (Newton's recursion) it contains
`x_i^{2r} + x_{i+1}^{2r}` and `(x_i^{2r} + x_{i+1}^{2r})(x_i - x_{i+1})`.  Together with the shift
`P(m+a,m+b) = (-1)^{ma+m} x_i^m x_{i+1}^m P(a,b)` this gives the three cases of Lemma 4.4
(`shuffle_one`, `shuffle_even`, `shuffle_odd`), in every rank `n+2` and position `i`.

* `big_shuffle_false`: the big odd shuffle (4.27), with the printed coefficients
  `(-1)^{m(j+1)}`, fails at `m = 0`, `k = 7`.
* `big_shuffle`: (4.27) holds with the coefficients `(-1)^{C(j,2)+(m+1)(j+1)}`.
* `divided_monomial_balanced`, `divided_monomial_ascent_mem_span`: the same statements for
  monomials with arbitrary spectator exponents.
-/
namespace OddMath.Frontier.ShuffleLemma
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open AllRankDivided LongestDivided

variable {n : ℕ}

/-! ### Algebra of the kernel -/

/-- The kernel of `∂_i` is closed under products. -/
theorem divided_mul_eq_zero (i : Fin (n+1)) {f g : SkewPolynomial (n+2)}
    (hf : divided i f = 0) (hg : divided i g = 0) : divided i (f * g) = 0 := by
  rw [divided_mul, hf, hg, zero_mul, mul_zero, add_zero]

/-- Moving a power of one generator past a power of a distinct generator. -/
theorem pow_mul_pow_swap {N : ℕ} (i j : Fin N) (h : i ≠ j) (a b : ℕ) :
    generator j ^ b * generator i ^ a =
      (-1 : ℤ)^(a*b) • (generator i ^ a * generator j ^ b) := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, ← mul_assoc,
        generator_mul_pow i j h a, smul_mul_assoc, smul_smul, mul_assoc, ← pow_succ',
        ← pow_add]
      congr 2

theorem neg_one_pow_mul_self (m : ℕ) : (-1 : ℤ)^(m*m) = (-1)^m := by
  rcases Nat.even_or_odd m with h | h
  · rw [h.neg_one_pow, (h.mul_right m).neg_one_pow]
  · rw [h.neg_one_pow, (h.mul h).neg_one_pow]

theorem s_castSucc (i : Fin (n+1)) : s i (generator i.castSucc) = -generator i.succ := by
  rw [s_generator, Equiv.swap_apply_left]

theorem s_succ (i : Fin (n+1)) : s i (generator i.succ) = -generator i.castSucc := by
  rw [s_generator, Equiv.swap_apply_right]

/-- The twist of a balanced adjacent monomial. -/
theorem s_balanced (i : Fin (n+1)) (m : ℕ) :
    s i (generator i.castSucc ^ m * generator i.succ ^ m) =
      (-1 : ℤ)^m • (generator i.castSucc ^ m * generator i.succ ^ m) := by
  rw [map_mul, map_pow, map_pow, s_castSucc, s_succ]
  rcases Nat.even_or_odd m with h | h
  · rw [h.neg_pow, h.neg_pow, pow_mul_pow_swap _ _ (adjacent_ne i), neg_one_pow_mul_self]
  · rw [h.neg_pow, h.neg_pow, neg_mul_neg, pow_mul_pow_swap _ _ (adjacent_ne i),
      neg_one_pow_mul_self]

/-- Balanced factors pass through `∂_i` up to sign. -/
theorem divided_balanced_mul (i : Fin (n+1)) (m : ℕ) (f : SkewPolynomial (n+2)) :
    divided i (generator i.castSucc ^ m * generator i.succ ^ m * f) =
      (-1 : ℤ)^m • (generator i.castSucc ^ m * generator i.succ ^ m * divided i f) := by
  rw [divided_mul, divided_balanced, zero_mul, zero_add, s_balanced, smul_mul_assoc]

/-- The shift: common powers factor out of `P(p,q)`. -/
theorem divided_shift (i : Fin (n+1)) (m a b : ℕ) :
    divided i (generator i.castSucc ^ (m+a) * generator i.succ ^ (m+b)) =
      (-1 : ℤ)^(m*a + m) • (generator i.castSucc ^ m * generator i.succ ^ m *
        divided i (generator i.castSucc ^ a * generator i.succ ^ b)) := by
  have h : generator i.castSucc ^ (m+a) * generator i.succ ^ (m+b) =
      (-1 : ℤ)^(m*a) • (generator i.castSucc ^ m * generator i.succ ^ m *
        (generator i.castSucc ^ a * generator i.succ ^ b)) := by
    rw [pow_add, pow_add, mul_assoc, ← mul_assoc (generator i.castSucc ^ a),
      pow_mul_pow_swap _ _ (adjacent_ne i).symm, smul_mul_assoc, mul_smul_comm]
    simp only [mul_assoc]
  rw [h, map_zsmul, divided_balanced_mul, smul_smul, ← pow_add]

/-! ### Kernel elements -/

theorem divided_castSucc (i : Fin (n+1)) : divided i (generator i.castSucc) = 1 := by
  rw [divided_generator, if_pos (Or.inl rfl)]

theorem divided_succ (i : Fin (n+1)) : divided i (generator i.succ) = 1 := by
  rw [divided_generator, if_pos (Or.inr rfl)]

theorem divided_sub_generator (i : Fin (n+1)) :
    divided i (generator i.castSucc - generator i.succ) = 0 := by
  rw [map_sub, divided_castSucc, divided_succ, sub_self]

theorem sub_mul_sub_generator (i : Fin (n+1)) :
    (generator i.castSucc - generator i.succ) * (generator i.castSucc - generator i.succ) =
      generator i.castSucc ^ 2 + generator i.succ ^ 2 := by
  have hc : generator i.succ * generator i.castSucc =
      -(generator i.castSucc * generator i.succ) :=
    OddMath.SkewPolynomial.generator_anticommute _ _ (adjacent_ne i).symm
  rw [sub_mul, mul_sub, mul_sub, hc, sq, sq]
  abel

theorem divided_sq_add_sq (i : Fin (n+1)) :
    divided i (generator i.castSucc ^ 2 + generator i.succ ^ 2) = 0 := by
  rw [← sub_mul_sub_generator]
  exact divided_mul_eq_zero i (divided_sub_generator i) (divided_sub_generator i)

/-- A generator square commutes with every other generator. -/
theorem commute_sq_generator {N : ℕ} (i j : Fin N) (h : i ≠ j) :
    Commute (generator i ^ 2) (generator j) := by
  have := generator_mul_pow i j h 2
  rw [neg_one_sq, one_smul] at this
  exact this.symm

/-- Newton's recursion for two commuting elements. -/
theorem pow_add_pow_succ_succ {R : Type*} [Ring R] {u v : R} (hc : Commute u v) (r : ℕ) :
    u^(r+2) + v^(r+2) = (u + v) * (u^(r+1) + v^(r+1)) - u * v * (u^r + v^r) := by
  have e1 : u * v * u^r = v * u^(r+1) := by rw [hc.eq, mul_assoc, ← pow_succ']
  have e2 : u * v * v^r = u * v^(r+1) := by rw [mul_assoc, ← pow_succ']
  rw [add_mul, mul_add, mul_add, mul_add, e1, e2, ← pow_succ', ← pow_succ' v]
  abel

/-- Even power sums are killed. -/
theorem divided_even_power_sum (i : Fin (n+1)) (r : ℕ) :
    divided i (generator i.castSucc ^ (2*r) + generator i.succ ^ (2*r)) = 0 := by
  simp only [pow_mul]
  have hc : Commute (generator i.castSucc ^ 2) (generator i.succ ^ 2) :=
    (commute_sq_generator _ _ (adjacent_ne i)).pow_right 2
  have hprod : divided i (generator i.castSucc ^ 2 * generator i.succ ^ 2) = 0 :=
    divided_balanced i 2
  induction r using Nat.strong_induction_on with
  | _ r ih =>
      match r, ih with
      | 0, _ => rw [pow_zero, pow_zero, map_add, divided_one, add_zero]
      | 1, _ => rw [pow_one, pow_one]; exact divided_sq_add_sq i
      | r+2, ih =>
          rw [pow_add_pow_succ_succ hc, map_sub,
            divided_mul_eq_zero i (divided_sq_add_sq i) (ih (r+1) (by omega)),
            divided_mul_eq_zero i hprod (ih r (by omega)), sub_zero]

/-- The odd kernel element `(x_i^{2r} + x_{i+1}^{2r})(x_i - x_{i+1})`. -/
theorem divided_odd_kernel (i : Fin (n+1)) (r : ℕ) :
    divided i (generator i.castSucc ^ (2*r+1) - generator i.castSucc ^ (2*r) * generator i.succ +
      generator i.castSucc * generator i.succ ^ (2*r) - generator i.succ ^ (2*r+1)) = 0 := by
  have hc : Commute (generator i.succ ^ (2*r)) (generator i.castSucc) := by
    rw [pow_mul]
    exact (commute_sq_generator _ _ (adjacent_ne i).symm).pow_left r
  have he : generator i.castSucc ^ (2*r+1) - generator i.castSucc ^ (2*r) * generator i.succ +
      generator i.castSucc * generator i.succ ^ (2*r) - generator i.succ ^ (2*r+1) =
      (generator i.castSucc ^ (2*r) + generator i.succ ^ (2*r)) *
        (generator i.castSucc - generator i.succ) := by
    rw [add_mul, mul_sub, mul_sub, ← hc.eq, ← pow_succ, ← pow_succ]
    abel
  rw [he]
  exact divided_mul_eq_zero i (divided_even_power_sum i r) (divided_sub_generator i)

/-! ### Lemma 4.4 -/

theorem neg_one_pow_mul_even {m k : ℕ} (hk : Even k) : (-1 : ℤ)^(m*k) = 1 := by
  rw [pow_mul', hk.neg_one_pow, one_pow]

theorem neg_one_pow_mul_odd {m k : ℕ} (hk : Odd k) : (-1 : ℤ)^(m*k) = (-1)^m := by
  rw [pow_mul', hk.neg_one_pow]

theorem neg_one_pow_add_self (m : ℕ) : (-1 : ℤ)^(m+m) = 1 := by
  rw [← two_mul, pow_mul, neg_one_sq, one_pow]

/-- EKL Lemma 4.4, case `k = 1`. -/
theorem shuffle_one (i : Fin (n+1)) (m : ℕ) :
    divided i (generator i.castSucc ^ m * generator i.succ ^ (m+1)) =
      (-1 : ℤ)^m • divided i (generator i.castSucc ^ (m+1) * generator i.succ ^ m) := by
  have h1 := divided_shift i m 0 1
  have h2 := divided_shift i m 1 0
  rw [add_zero] at h1 h2
  rw [h1, h2, mul_zero, zero_add, mul_one, neg_one_pow_add_self, one_smul, pow_zero, pow_zero,
    pow_one, pow_one, one_mul, mul_one, divided_castSucc, divided_succ]

/-- EKL Lemma 4.4, case `k` even (the case `k = 0` is included). -/
theorem shuffle_even (i : Fin (n+1)) (m k : ℕ) (hk : Even k) :
    divided i (generator i.castSucc ^ m * generator i.succ ^ (m+k)) =
      -divided i (generator i.castSucc ^ (m+k) * generator i.succ ^ m) := by
  have h1 := divided_shift i m 0 k
  have h2 := divided_shift i m k 0
  rw [add_zero] at h1 h2
  obtain ⟨r, rfl⟩ := hk
  have hs : (-1 : ℤ)^(m*(r+r)+m) = (-1)^(m*0+m) := by
    rw [pow_add, pow_add, neg_one_pow_mul_even ⟨r, rfl⟩, mul_zero, pow_zero]
  have h0 := divided_even_power_sum i r
  rw [map_add, add_eq_zero_iff_eq_neg, two_mul] at h0
  rw [h1, h2, hs, pow_zero, pow_zero, one_mul, mul_one, h0, mul_neg, smul_neg, neg_neg]

/-- EKL Lemma 4.4, case `k` odd, `k ≥ 3`. -/
theorem shuffle_odd (i : Fin (n+1)) (m k : ℕ) (hk : Odd k) (h3 : 3 ≤ k) :
    divided i (generator i.castSucc ^ m * generator i.succ ^ (m+k)) =
      (-1 : ℤ)^m • divided i (generator i.castSucc ^ (m+k) * generator i.succ ^ m) -
      divided i (generator i.castSucc ^ (m+k-1) * generator i.succ ^ (m+1)) +
      (-1 : ℤ)^m • divided i (generator i.castSucc ^ (m+1) * generator i.succ ^ (m+k-1)) := by
  obtain ⟨r, rfl⟩ := hk
  have hsub : m + (2*r+1) - 1 = m + 2*r := by omega
  have h1 := divided_shift i m 0 (2*r+1)
  have h2 := divided_shift i m (2*r+1) 0
  have h3' := divided_shift i m (2*r) 1
  have h4 := divided_shift i m 1 (2*r)
  rw [add_zero] at h1 h2
  have s0 : (-1 : ℤ)^(m*0+m) = (-1)^m := by rw [mul_zero, zero_add]
  have s1 : (-1 : ℤ)^(m*(2*r+1)+m) = 1 := by
    rw [pow_add, neg_one_pow_mul_odd ⟨r, rfl⟩, ← pow_add, neg_one_pow_add_self]
  have s2 : (-1 : ℤ)^(m*(2*r)+m) = (-1)^m := by
    rw [pow_add, neg_one_pow_mul_even ⟨r, two_mul r⟩, one_mul]
  have s3 : (-1 : ℤ)^(m*1+m) = 1 := by rw [mul_one, neg_one_pow_add_self]
  rw [s0, pow_zero, one_mul] at h1
  rw [s1, pow_zero, mul_one, one_smul] at h2
  rw [s2, pow_one] at h3'
  rw [s3, pow_one, one_smul] at h4
  have h0 := divided_odd_kernel i r
  rw [map_sub, map_add, map_sub, sub_eq_zero] at h0
  rw [hsub, h1, h2, h3', h4, ← h0, mul_add, mul_sub, smul_add, smul_sub]

/-! ### Monomials -/

/-- Crossing-free concatenations carry no sign. -/
theorem skewSign_eq_one {N : ℕ} (u v : Fin N → ℕ) (h : ∀ a b, b < a → u a = 0 ∨ v b = 0) :
    OddMath.skewSign u v = 1 := by
  unfold OddMath.skewSign OddMath.crossingCount
  rw [Finset.sum_eq_zero, pow_zero]
  intro a _
  apply Finset.sum_eq_zero
  intro b hb
  rcases h a b (Finset.mem_filter.1 hb).2 with h | h <;> simp [h]

theorem mul_monomial_of_noncrossing {N : ℕ} (u v : Fin N → ℕ)
    (h : ∀ a b, b < a → u a = 0 ∨ v b = 0) :
    monomial u 1 * monomial v 1 = monomial (u + v) 1 := by
  change OddMath.SkewPolynomial.mul _ _ = _
  rw [OddMath.SkewPolynomial.mul_monomial, skewSign_eq_one u v h, one_mul, one_mul]

/-- The adjacent pair monomial in normal order. -/
theorem pair_monomial (i : Fin (n+1)) (p q : ℕ) :
    generator i.castSucc ^ p * generator i.succ ^ q =
      monomial (p • OddMath.SkewPolynomial.expSingle i.castSucc +
        q • OddMath.SkewPolynomial.expSingle i.succ) 1 := by
  rw [PbwL4.pow_form, PbwL4.pow_form]
  apply mul_monomial_of_noncrossing
  intro a b hba
  by_cases ha : a = i.castSucc
  · right
    have hb : i.succ ≠ b := by
      rintro rfl
      rw [ha, Fin.lt_iff_val_lt_val] at hba
      simp at hba
    simp [OddMath.SkewPolynomial.expSingle, hb]
  · left
    simp [OddMath.SkewPolynomial.expSingle, Ne.symm ha]

theorem pair_ne_zero (i : Fin (n+1)) (p q : ℕ) {c : ℤ} (hc : c ≠ 0) :
    c • (generator i.castSucc ^ p * generator i.succ ^ q) ≠ 0 := by
  rw [pair_monomial, ← PbwL4.monomial_smul]
  exact Finsupp.single_ne_zero.mpr hc

/-! ### The big odd shuffle (4.27) -/

/-- The big odd shuffle (4.27) as printed fails (at `m = 0`, `k = 7`, in every rank and
position). -/
theorem big_shuffle_false (i : Fin (n+1)) :
    ¬ ∀ m k : ℕ, Odd k → 3 ≤ k →
      divided i (generator i.castSucc ^ m * generator i.succ ^ (m+k)) =
        (-1 : ℤ)^m • divided i (generator i.castSucc ^ (m+k) * generator i.succ ^ m) -
        (2 : ℤ) • ∑ j ∈ Finset.Icc 1 (k/2), (-1 : ℤ)^(m*(j+1)) •
          divided i (generator i.castSucc ^ (m+k-j) * generator i.succ ^ (m+j)) := by
  intro H
  have hp := H 0 7 ⟨3, rfl⟩ (by norm_num)
  have h0 := shuffle_odd i 0 7 ⟨3, rfl⟩ (by norm_num)
  have h1 := shuffle_odd i 1 5 ⟨2, rfl⟩ (by norm_num)
  have h2 := shuffle_odd i 2 3 ⟨1, rfl⟩ le_rfl
  have h3 := shuffle_one i 3
  have hs := divided_step i 3
  have hI : Finset.Icc 1 3 = {1, 2, 3} := rfl
  norm_num [hI] at hp h0 h1 h2 h3 hs
  simp only [two_mul] at hp
  have h4 : (4 : ℤ) • (generator i.castSucc ^ 3 * generator i.succ ^ 3) = 0 := by
    rw [← hs]
    linear_combination (norm := module) hp - h0 - h1 + h2 + h3
  exact pair_ne_zero i 3 3 (by norm_num) h4

/-- Range-indexed form of the corrected big odd shuffle, `k = 2r+1`. -/
theorem big_shuffle_range (i : Fin (n+1)) (r : ℕ) : ∀ m : ℕ,
    divided i (generator i.castSucc ^ m * generator i.succ ^ (m+(2*r+1))) =
      (-1 : ℤ)^m • divided i (generator i.castSucc ^ (m+(2*r+1)) * generator i.succ ^ m) -
      (2 : ℤ) • ∑ j ∈ Finset.range r, (-1 : ℤ)^((j+1).choose 2 + (m+1)*(j+2)) •
        divided i (generator i.castSucc ^ (m+(2*r+1)-(j+1)) * generator i.succ ^ (m+(j+1))) := by
  induction r with
  | zero =>
      intro m
      rw [Finset.sum_range_zero, smul_zero, sub_zero]
      exact shuffle_one i m
  | succ r ih =>
      intro m
      have h := shuffle_odd i m (2*(r+1)+1) ⟨r+1, rfl⟩ (by omega)
      rw [show m + (2*(r+1)+1) - 1 = m + 1 + (2*r+1) by omega] at h
      rw [h, ih (m+1), Finset.sum_range_succ']
      have hc0 : (-1 : ℤ)^((0+1).choose 2 + (m+1)*(0+2)) = 1 := by
        rw [Nat.choose_eq_zero_of_lt (by norm_num), zero_add, pow_mul', neg_one_sq, one_pow]
      rw [hc0, one_smul, show m + (2*(r+1)+1) - (0+1) = m + 1 + (2*r+1) by omega,
        show m + (0+1) = m + 1 by omega]
      have hsum : ∑ j ∈ Finset.range r, (-1 : ℤ)^((j+1+1).choose 2 + (m+1)*(j+1+2)) •
          divided i (generator i.castSucc ^ (m+(2*(r+1)+1)-(j+1+1)) *
            generator i.succ ^ (m+(j+1+1))) =
          ∑ j ∈ Finset.range r, (-1 : ℤ)^m • ((-1 : ℤ)^((j+1).choose 2 + (m+1+1)*(j+2)) •
          divided i (generator i.castSucc ^ (m+1+(2*r+1)-(j+1)) *
            generator i.succ ^ (m+1+(j+1)))) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_smul, ← pow_add, show m + (2*(r+1)+1) - (j+1+1) = m+1+(2*r+1)-(j+1) by omega,
          show m + (j+1+1) = m+1+(j+1) by omega, Nat.choose_succ_succ', Nat.choose_one_right]
        congr 2
        ring
      rw [hsum, ← Finset.smul_sum, pow_succ (-1 : ℤ) m, mul_neg_one, neg_smul, smul_sub,
        smul_neg, smul_smul, ← pow_add, neg_one_pow_add_self, one_smul]
      module

/-- The corrected big odd shuffle: (4.27) holds with coefficient `(-1)^(C(j,2)+(m+1)(j+1))`
(for every odd `k`; the sum is empty when `k = 1`). -/
theorem big_shuffle (i : Fin (n+1)) (m k : ℕ) (hk : Odd k) :
    divided i (generator i.castSucc ^ m * generator i.succ ^ (m+k)) =
      (-1 : ℤ)^m • divided i (generator i.castSucc ^ (m+k) * generator i.succ ^ m) -
      (2 : ℤ) • ∑ j ∈ Finset.Icc 1 (k/2), (-1 : ℤ)^(j.choose 2 + (m+1)*(j+1)) •
        divided i (generator i.castSucc ^ (m+k-j) * generator i.succ ^ (m+j)) := by
  obtain ⟨r, rfl⟩ := hk
  rw [show (2*r+1)/2 = r by omega, ← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range,
    Nat.succ_sub_one, big_shuffle_range i r m]
  simp only [add_comm 1]

/-! ### Ascents are combinations of descents -/

/-- Pair-level form: `P(p, p+k)`, `k > 0`, is a combination of descents `P(p', q')` with
`p ≤ q' < p' ≤ p+k` and `p' + q' = 2p + k`. -/
theorem pair_ascent_mem_span (i : Fin (n+1)) (k : ℕ) : ∀ p : ℕ, 0 < k →
    divided i (generator i.castSucc ^ p * generator i.succ ^ (p+k)) ∈ Submodule.span ℤ
      ((fun pq : ℕ × ℕ => divided i (generator i.castSucc ^ pq.1 * generator i.succ ^ pq.2)) ''
        {pq | pq.2 < pq.1 ∧ p ≤ pq.2 ∧ pq.1 ≤ p+k ∧ pq.1 + pq.2 = p + (p+k)}) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro p hk
      have mem : ∀ a b : ℕ, b < a → p ≤ b → a ≤ p+k → a + b = p + (p+k) →
          divided i (generator i.castSucc ^ a * generator i.succ ^ b) ∈ Submodule.span ℤ
            ((fun pq : ℕ × ℕ => divided i (generator i.castSucc ^ pq.1 * generator i.succ ^ pq.2)) ''
              {pq | pq.2 < pq.1 ∧ p ≤ pq.2 ∧ pq.1 ≤ p+k ∧ pq.1 + pq.2 = p + (p+k)}) :=
        fun a b h1 h2 h3 h4 => Submodule.subset_span ⟨(a, b), ⟨h1, h2, h3, h4⟩, rfl⟩
      rcases Nat.even_or_odd k with he | ho
      · rw [shuffle_even i p k he]
        exact Submodule.neg_mem _ (mem _ _ (by omega) le_rfl le_rfl (by omega))
      · by_cases h1 : k = 1
        · subst h1
          rw [shuffle_one i p]
          exact Submodule.smul_mem _ _ (mem _ _ (by omega) le_rfl le_rfl (by omega))
        · have h3 : 3 ≤ k := by obtain ⟨r, rfl⟩ := ho; omega
          rw [shuffle_odd i p k ho h3]
          refine Submodule.add_mem _ (Submodule.sub_mem _
            (Submodule.smul_mem _ _ (mem _ _ (by omega) le_rfl le_rfl (by omega)))
            (mem _ _ (by omega) (by omega) (by omega) (by omega))) (Submodule.smul_mem _ _ ?_)
          have hIH := ih (k-2) (by omega) (p+1) (by omega)
          rw [show p + 1 + (k-2) = p + k - 1 by omega] at hIH
          refine Submodule.span_mono ?_ hIH
          rintro _ ⟨⟨a, b⟩, ⟨hb1, hb2, hb3, hb4⟩, rfl⟩
          exact ⟨(a, b), ⟨hb1, by omega, by omega, by omega⟩, rfl⟩

/-! ### Spectators -/

/-- Exponents strictly left of the pair. -/
def lowPart (i : Fin (n+1)) (γ : Fin (n+2) → ℕ) : Fin (n+2) → ℕ :=
  fun j => if j < i.castSucc then γ j else 0

/-- Exponents strictly right of the pair. -/
def highPart (i : Fin (n+1)) (γ : Fin (n+2) → ℕ) : Fin (n+2) → ℕ :=
  fun j => if i.succ < j then γ j else 0

theorem exponent_decompose (i : Fin (n+1)) (γ : Fin (n+2) → ℕ) :
    γ = lowPart i γ + (γ i.castSucc • OddMath.SkewPolynomial.expSingle i.castSucc +
      γ i.succ • OddMath.SkewPolynomial.expSingle i.succ) + highPart i γ := by
  funext j
  simp only [lowPart, highPart, Pi.add_apply, Pi.smul_apply, OddMath.SkewPolynomial.expSingle,
    smul_eq_mul, Fin.lt_iff_val_lt_val, Fin.ext_iff, Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> first | omega |
    (simp only [zero_add, add_zero, mul_one, mul_zero]; congr 1; ext
     simp only [Fin.coe_castSucc, Fin.val_succ]; omega)

theorem monomial_decompose (i : Fin (n+1)) (γ : Fin (n+2) → ℕ) :
    monomial γ 1 = monomial (lowPart i γ) 1 *
      (generator i.castSucc ^ (γ i.castSucc) * generator i.succ ^ (γ i.succ)) *
      monomial (highPart i γ) 1 := by
  rw [pair_monomial, mul_monomial_of_noncrossing, mul_monomial_of_noncrossing,
    ← exponent_decompose]
  · intro a b hba
    by_cases hb : i.succ < b
    · left
      have ha : i.succ < a := lt_trans hb hba
      have ha1 : a ≠ i.castSucc := by
        rintro rfl
        rw [Fin.lt_iff_val_lt_val] at ha
        simp at ha
      simp [lowPart, OddMath.SkewPolynomial.expSingle, ha.ne, ha1.symm,
        not_lt_of_gt (lt_trans (Fin.castSucc_lt_succ i) ha)]
    · right
      simp [highPart, hb]
  · intro a b hba
    by_cases ha : a < i.castSucc
    · right
      have hb : b < i.castSucc := lt_trans hba ha
      have hb1 : i.succ ≠ b := by
        rintro rfl
        exact absurd (lt_trans hb (Fin.castSucc_lt_succ i)) (lt_irrefl _)
      simp [OddMath.SkewPolynomial.expSingle, hb.ne', hb1]
    · left
      simp [lowPart, ha]

/-- Monomials in the spectator variables are killed. -/
theorem divided_monomial_spectator (i : Fin (n+1)) (d : ℕ) : ∀ σ : Fin (n+2) → ℕ,
    ∑ j, σ j = d → σ i.castSucc = 0 → σ i.succ = 0 → divided i (monomial σ 1) = 0 := by
  induction d with
  | zero =>
      intro σ hd _ _
      have hσ : σ = 0 := by
        funext j
        exact (Finset.sum_eq_zero_iff.mp hd) j (Finset.mem_univ j)
      subst hσ
      exact divided_one i
  | succ d ih =>
      intro σ hd hl hr
      obtain ⟨j, hj⟩ : ∃ j, σ j ≠ 0 := by
        by_contra h
        push_neg at h
        simp [h] at hd
      let σ' := Function.update σ j (σ j - 1)
      have hσ : σ = σ' + OddMath.SkewPolynomial.expSingle j := by
        funext k
        by_cases hk : k = j
        · subst hk
          simp [σ', OddMath.SkewPolynomial.expSingle]
          omega
        · simp [σ', OddMath.SkewPolynomial.expSingle, hk, Ne.symm hk]
      have hjl : j ≠ i.castSucc := by rintro rfl; exact hj hl
      have hjr : j ≠ i.succ := by rintro rfl; exact hj hr
      have hsum : ∑ k, σ' k = d := by
        rw [hσ] at hd
        simp only [Pi.add_apply, Finset.sum_add_distrib] at hd
        simp [OddMath.SkewPolynomial.expSingle] at hd
        omega
      have h' : divided i (monomial σ' 1) = 0 :=
        ih σ' hsum (by simp [σ', Function.update_of_ne hjl.symm, hl])
          (by simp [σ', Function.update_of_ne hjr.symm, hr])
      have hg : divided i (generator j) = 0 := by
        rw [divided_generator, if_neg (by tauto)]
      have hprod := divided_mul_eq_zero i h' hg
      have hm : monomial σ' 1 * generator j =
          OddMath.skewSign σ' (OddMath.SkewPolynomial.expSingle j) • monomial σ 1 := by
        change OddMath.SkewPolynomial.mul (monomial σ' 1)
          (monomial (OddMath.SkewPolynomial.expSingle j) 1) = _
        rw [OddMath.SkewPolynomial.mul_monomial, one_mul, one_mul, PbwL4.monomial_smul, ← hσ]
      rw [hm, map_zsmul] at hprod
      have hsq : OddMath.skewSign σ' (OddMath.SkewPolynomial.expSingle j) *
          OddMath.skewSign σ' (OddMath.SkewPolynomial.expSingle j) = 1 := by
        rw [OddMath.skewSign, ← mul_pow, neg_one_mul, neg_neg, one_pow]
      have := congrArg (OddMath.skewSign σ' (OddMath.SkewPolynomial.expSingle j) • ·) hprod
      simpa only [smul_smul, hsq, one_smul, smul_zero] using this

/-- `∂_i` on a monomial: spectators factor out. -/
theorem divided_monomial_eq (i : Fin (n+1)) (γ : Fin (n+2) → ℕ) :
    divided i (monomial γ 1) = s i (monomial (lowPart i γ) 1) *
      (divided i (generator i.castSucc ^ (γ i.castSucc) * generator i.succ ^ (γ i.succ)) *
        monomial (highPart i γ) 1) := by
  have hlt : ¬ i.succ < i.castSucc := not_lt_of_gt (Fin.castSucc_lt_succ i)
  have hL : divided i (monomial (lowPart i γ) 1) = 0 :=
    divided_monomial_spectator i _ _ rfl (by simp [lowPart])
      (by simp [lowPart, hlt])
  have hR : divided i (monomial (highPart i γ) 1) = 0 :=
    divided_monomial_spectator i _ _ rfl (by simp [highPart, hlt])
      (by simp [highPart])
  rw [monomial_decompose i γ, mul_assoc, divided_mul, hL, zero_mul, zero_add, divided_mul, hR,
    mul_zero, add_zero]

/-! ### Interface with spectators -/

/-- Equal adjacent exponents are killed. -/
theorem divided_monomial_balanced (i : Fin (n+1)) (γ : Fin (n+2) → ℕ) (c : ℤ)
    (h : γ i.castSucc = γ i.succ) : divided i (monomial γ c) = 0 := by
  rw [PbwL4.monomial_smul, map_zsmul, divided_monomial_eq, h, divided_balanced, zero_mul,
    mul_zero, smul_zero]

/-- An ascent is a combination of descents in the same range. -/
theorem divided_monomial_ascent_mem_span (i : Fin (n+1)) (γ : Fin (n+2) → ℕ)
    (h : γ i.castSucc < γ i.succ) :
    divided i (monomial γ 1) ∈ Submodule.span ℤ
      ((fun γ' => divided i (monomial γ' 1)) ''
        {γ' | (∀ j, j ≠ i.castSucc → j ≠ i.succ → γ' j = γ j) ∧
              γ' i.succ < γ' i.castSucc ∧ γ i.castSucc ≤ γ' i.succ ∧ γ' i.castSucc ≤ γ i.succ ∧
              γ' i.castSucc + γ' i.succ = γ i.castSucc + γ i.succ}) := by
  set T : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2) :=
    (LinearMap.mulLeft ℤ (s i (monomial (lowPart i γ) 1))).comp
      (LinearMap.mulRight ℤ (monomial (highPart i γ) 1))
  have hTapp : ∀ f, T f = s i (monomial (lowPart i γ) 1) * (f * monomial (highPart i γ) 1) :=
    fun _ => rfl
  have hpair := pair_ascent_mem_span i (γ i.succ - γ i.castSucc) (γ i.castSucc) (by omega)
  rw [show γ i.castSucc + (γ i.succ - γ i.castSucc) = γ i.succ by omega] at hpair
  have hmap := Submodule.mem_map_of_mem (f := T) hpair
  rw [← Submodule.span_image, hTapp, ← divided_monomial_eq] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨_, ⟨⟨a, b⟩, ⟨h1, h2, h3, h4⟩, rfl⟩, rfl⟩
  let γ' : Fin (n+2) → ℕ := fun j => if j = i.castSucc then a else if j = i.succ then b else γ j
  have hne : i.succ ≠ i.castSucc := (adjacent_ne i).symm
  have hc : γ' i.castSucc = a := by simp [γ']
  have hs : γ' i.succ = b := by simp [γ', hne]
  have hoff : ∀ j, j ≠ i.castSucc → j ≠ i.succ → γ' j = γ j := by
    intro j hj1 hj2
    simp [γ', hj1, hj2]
  refine ⟨γ', ⟨hoff, by omega, by omega, by omega, by omega⟩, ?_⟩
  have hlow : lowPart i γ' = lowPart i γ := by
    funext j
    by_cases hj : j < i.castSucc
    · simp only [lowPart, if_pos hj]
      exact hoff j hj.ne (lt_trans hj (Fin.castSucc_lt_succ i)).ne
    · simp only [lowPart, if_neg hj]
  have hhigh : highPart i γ' = highPart i γ := by
    funext j
    by_cases hj : i.succ < j
    · simp only [highPart, if_pos hj]
      exact hoff j (lt_trans (Fin.castSucc_lt_succ i) hj).ne' hj.ne'
    · simp only [highPart, if_neg hj]
  simp only [divided_monomial_eq i γ', hlow, hhigh, hc, hs, hTapp]

end OddMath.Frontier.ShuffleLemma
