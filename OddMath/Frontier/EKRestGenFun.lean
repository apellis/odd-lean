import OddMath.Frontier.EKAutomorphisms

/-! # EK (2.22), (2.23) and the `ℤ/2`-grading reading of `ψ₂`

EK arXiv:1107.5610v2, §2.3, p. 19, integral q = -1, in the radical quotient `Q`.

* (2.22): `Σ_{k=0}^n (-1)^{k(n-k)} ψ₂(e_{n-k}) h_k = 0` for `n ≥ 1` (`eq_2_22`).
  Proof: apply `ψ₂` to (2.5) and use `C(a+1,2) + C(b+1,2) ≡ C(a+b+1,2) + ab (mod 2)`.
* (2.23): `ψ₂(E(t)) H(t) = 1` in `Λ[t]`, `t` of degree 1 and super-central
  (`t x = (-1)^{deg x} x t` for homogeneous `x`), `ψ₂(t) = t`. For `a, b` homogeneous,
  `(a tⁱ)(b tʲ) = (-1)^{i deg b} ab t^{i+j}`; since `deg h_j = j`, the coefficient of `tⁿ` in
  `ψ₂(E(t))H(t)` is `superCoeff n = Σ_{i+j=n} (-1)^{ij} ψ₂(e_i) h_j`. The ring `Λ[t]` itself is
  not constructed; (2.23) is stated coefficientwise (`eq_2_23`), and its equivalence with (2.22)
  is `eq_2_23_iff`.
* p. 19: with `h_n` in `ℤ/2`-degree `0` if `n ≡ 0, 3 (mod 4)` and `1` if `n ≡ 1, 2 (mod 4)`,
  `ψ₂` is `+1` on degree-`0` words and `-1` on degree-`1` words (`psi2_word`).
-/

noncomputable section
open scoped BigOperators

namespace OddMath.Frontier.EKRest
open EKRadicalQuotient EKElementaryQuotient EKAutomorphisms

/-- EK (2.5) in `Q`: `Σ_{k=0}^n (-1)^{C(k+1,2)} e_k h_{n-k} = 0`, `n ≥ 1`. -/
theorem eq_2_5 (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ ((k + 1).choose 2) • (e k * h (n - k)) = 0 := by
  have hh := congrArg pi (CompleteElementary.elementary_complete_inverse_range n hn)
  rw [map_sum, map_zero] at hh
  rw [← hh]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_mul, map_mul, map_pow, map_neg, map_one, zsmul_eq_mul, mul_assoc]
  push_cast
  rfl

theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

theorem choose_add (a b : ℕ) :
    (a + 1).choose 2 + (b + 1).choose 2 + a * b = (a + b + 1).choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [choose_two_succ (b + 1), show a + (b + 1) + 1 = (a + b + 1) + 1 by omega,
      choose_two_succ (a + b + 1), ← ih]
    ring

theorem choose_parity (a b : ℕ) :
    (-1 : ℤ) ^ ((a + 1).choose 2 + (b + 1).choose 2) =
      (-1 : ℤ) ^ ((a + b + 1).choose 2) * (-1 : ℤ) ^ (a * b) := by
  rw [← choose_add a b, pow_add _ (_ + _) (a * b), mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

/-- `ψ₂(e_k h_m) = s_k s_m ψ₂(e_k) h_m`, `s_n = (-1)^{C(n+1,2)}`. -/
theorem psi2_e_h (k m : ℕ) : psi2 (e k * h m) = s m • (psi2 (e k) * h m) := by
  rw [map_mul, psi2_h, mul_smul_comm]

/-- **EK (2.22), p. 19:** `Σ_{k=0}^n (-1)^{k(n-k)} ψ₂(e_{n-k}) h_k = 0` for `n ≥ 1`. -/
theorem eq_2_22 (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (k * (n - k)) • (psi2 (e (n - k)) * h k) = 0 := by
  have hh := congrArg psi2 (eq_2_5 n hn)
  rw [map_sum, map_zero, ← Finset.sum_range_reflect] at hh
  have key : ∀ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (k * (n - k)) • (psi2 (e (n - k)) * h k) =
      (-1 : ℤ) ^ ((n + 1).choose 2) •
        psi2 ((-1 : ℤ) ^ ((n + 1 - 1 - k + 1).choose 2) • (e (n + 1 - 1 - k) * h (n - (n + 1 - 1 - k)))) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [show n + 1 - 1 - k = n - k by omega, show n - (n - k) = k by omega, map_zsmul, psi2_e_h,
      smul_smul, smul_smul, s]
    congr 1
    rw [← pow_add, ← pow_add]
    apply neg_one_pow_congr
    have hc := choose_add (n - k) k
    rw [show n - k + k = n by omega] at hc
    rw [mul_comm k, Nat.even_iff, Nat.even_iff]
    omega
  rw [Finset.sum_congr rfl key, ← Finset.smul_sum, hh, smul_zero]

/-- The coefficient of `tⁿ` in `ψ₂(E(t)) H(t)`, `t` super-central of degree 1:
`Σ_{i+j=n} (-1)^{ij} ψ₂(e_i) h_j`. -/
def superCoeff (n : ℕ) : Q :=
  ∑ p ∈ Finset.antidiagonal n, (-1 : ℤ) ^ (p.1 * p.2) • (psi2 (e p.1) * h p.2)

theorem superCoeff_eq (n : ℕ) :
    superCoeff n = ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (k * (n - k)) • (psi2 (e (n - k)) * h k) := by
  rw [superCoeff, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (-1 : ℤ) ^ (i * j) • (psi2 (e i) * h j)), ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  rw [show n + 1 - 1 - k = n - k by omega, show n - (n - k) = k by omega, mul_comm]

/-- **EK (2.23), p. 19:** `ψ₂(E(t)) H(t) = 1`, coefficientwise. -/
theorem eq_2_23 (n : ℕ) : superCoeff n = if n = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [superCoeff, EKElementaryQuotient.e, EKElementaryQuotient.h]
  · rw [if_neg (by omega), superCoeff_eq, eq_2_22 n hn]

/-- EK p. 19: "(2.22) is equivalent to (2.23)". -/
theorem eq_2_23_iff : (∀ n, superCoeff n = if n = 0 then 1 else 0) ↔
    (∀ n, 0 < n → ∑ k ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ (k * (n - k)) • (psi2 (e (n - k)) * h k) = 0) := by
  constructor
  · intro H n hn
    rw [← superCoeff_eq, H n, if_neg (by omega)]
  · intro H n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact eq_2_23 0
    · rw [if_neg (by omega), superCoeff_eq, H n hn]

/-- The `ℤ/2`-degree of `h_n` (EK p. 19): `0` for `n ≡ 0, 3`, `1` for `n ≡ 1, 2 (mod 4)`. -/
def zdeg (n : ℕ) : ℕ := if n % 4 = 1 ∨ n % 4 = 2 then 1 else 0

theorem choose_mod_two (n : ℕ) : (n + 1).choose 2 % 2 = zdeg n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have h1 := ih m (by omega)
      rw [show m + 4 + 1 = m + 1 + 1 + 1 + 1 + 1 by omega, choose_two_succ, choose_two_succ,
        choose_two_succ, choose_two_succ]
      have hz : zdeg (m + 4) = zdeg m := by simp only [zdeg]; rw [show (m + 4) % 4 = m % 4 by omega]
      rw [hz]
      omega

theorem s_eq_zdeg (n : ℕ) : s n = (-1 : ℤ) ^ zdeg n := by
  rw [s]
  apply neg_one_pow_congr
  have h1 := choose_mod_two n
  have h2 : zdeg n ≤ 1 := by unfold zdeg; split_ifs <;> omega
  rw [Nat.even_iff, Nat.even_iff]
  omega

/-- **EK p. 19:** `ψ₂` is `(-1)^{ℤ/2-degree}` on every `h`-word. -/
theorem psi2_word (α : List ℕ) :
    psi2 (α.map h).prod = (-1 : ℤ) ^ (α.map zdeg).sum • (α.map h).prod := by
  induction α with
  | nil => simp
  | cons a α ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih, psi2_h, s_eq_zdeg, List.map_cons,
      List.sum_cons, pow_add, smul_mul_smul_comm]

end OddMath.Frontier.EKRest
