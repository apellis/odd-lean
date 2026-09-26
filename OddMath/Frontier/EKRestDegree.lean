import OddMath.Frontier.CompleteElementary
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # The degree count (5.1)–(5.2)

EK arXiv:1107.5610v2, §5.2, pp. 40–41. The degree of the Gram determinant of the form (2.1) in
degree `n` at unspecialised `q` is asserted to be

  `D = Σ_α (½ n(n-1) - Σ_i ½ α_i(α_i - 1)) = 2^{n-2} n(n-1) - ½ A_n`            (5.1)

with `A_n = Σ_α Σ_i α_i(α_i - 1)` (sums over the compositions `α` of `n`),

  `A_n = n(n-1) + Σ_{k=1}^{n-1} [2^{n-k-1} k(k-1) + A_{n-k}]`,   `A_n = 2 + 2ⁿ(n-2)`,

and hence `D = 2^{n-2}(n² - 3n + 4) - 1`                                           (5.2).

This file proves the combinatorial identities, for every `n` (with `n ≥ 1`, resp. `n ≥ 2`
where the printed formulas need it): `eq_5_1`, `A_recursion`, `A_closed`, `eq_5_2`.
`D` is the plain sum over Mathlib's `Composition n`; that it is the degree of the Gram
determinant is a separate statement about the form (2.1).
-/

open scoped BigOperators

namespace OddMath.Frontier.EKRest

/-- `D` of (5.1): `Σ_α (C(n,2) - Σ_i C(α_i,2))`. -/
def degD (n : ℕ) : ℤ :=
  ∑ α : Composition n, ((n.choose 2 : ℤ) - (α.blocks.map (fun a => (a.choose 2 : ℤ))).sum)

/-- `A_n = Σ_α Σ_i α_i(α_i - 1)`. -/
def sumA (n : ℕ) : ℤ :=
  ∑ α : Composition n, (α.blocks.map (fun a : ℕ => (a : ℤ) * ((a : ℤ) - 1))).sum

/-! ## Transfer to the list enumeration `CompleteElementary.compositions` -/

theorem sum_composition_list (n : ℕ) (g : List ℕ → ℤ) :
    ∑ α : Composition n, g α.blocks = ∑ l ∈ CompleteElementary.compositions n, g l := by
  apply Finset.sum_nbij (fun α => α.blocks)
  · intro α _
    exact (CompleteElementary.mem_compositions_iff n _).mpr
      ⟨fun a ha => α.blocks_pos ha, α.blocks_sum⟩
  · intro α _ β _ h
    exact Composition.ext h
  · intro l hl
    obtain ⟨hp, hs⟩ := (CompleteElementary.mem_compositions_iff n l).mp hl
    exact ⟨⟨l, fun {a} ha => hp a ha, hs⟩, Finset.mem_univ _, rfl⟩
  · intro α _; rfl

/-- Number of compositions, as a list count. -/
theorem card_compositions (n : ℕ) :
    ((CompleteElementary.compositions n).card : ℤ) = 2 ^ (n - 1) := by
  have h := sum_composition_list n (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, composition_card, nsmul_eq_mul, mul_one] at h
  rw [← h]
  push_cast; rfl

/-- Last-part recursion for list sums of an additive statistic. -/
theorem sum_last_part (n : ℕ) (f : ℕ → ℤ) :
    ∑ l ∈ CompleteElementary.compositions (n + 1), (l.map f).sum =
      ∑ k ∈ Finset.range (n + 1), (∑ l ∈ CompleteElementary.compositions k, (l.map f).sum +
        ((CompleteElementary.compositions k).card : ℤ) * f (n + 1 - k)) := by
  rw [CompleteElementary.compositions,
    Finset.sum_biUnion (CompleteElementary.composition_branches_disjoint n)]
  simp only [Finset.sum_image (fun _ _ _ _ h => List.append_cancel_right h),
    List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∑ l ∈ CompleteElementary.compositions k,
      (l.map f).sum) (n + 1), Fin.sum_univ_eq_sum_range
      (fun k => ((CompleteElementary.compositions k).card : ℤ) * f (n + 1 - k)) (n + 1)]

def fA (a : ℕ) : ℤ := (a : ℤ) * ((a : ℤ) - 1)

def Al (n : ℕ) : ℤ := ∑ l ∈ CompleteElementary.compositions n, (l.map fA).sum

theorem sumA_eq (n : ℕ) : sumA n = Al n := by
  unfold sumA Al; exact sum_composition_list n (fun l => (l.map fA).sum)


theorem Al_zero : Al 0 = 0 := by simp [Al, CompleteElementary.compositions]

def cc (k : ℕ) : ℤ := 2 ^ (k - 1)

theorem Al_succ (n : ℕ) :
    Al (n + 1) = ∑ k ∈ Finset.range (n + 1), (Al k + cc k * fA (n + 1 - k)) := by
  rw [Al, sum_last_part]
  apply Finset.sum_congr rfl
  intro k _
  rw [card_compositions]; rfl

theorem sum_cc (n : ℕ) : ∑ k ∈ Finset.range (n + 1), cc k = 2 ^ n := by
  induction n with
  | zero => simp [cc]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, cc, show n + 1 - 1 = n by omega, pow_succ]
    ring

theorem sum_cc_weighted (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), cc k * ((n : ℤ) + 1 - k) = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => simp [cc]
  | succ n ih =>
    have h1 : ∑ k ∈ Finset.range (n + 1 + 1), cc k * (((n + 1 : ℕ) : ℤ) + 1 - k) =
        ∑ k ∈ Finset.range (n + 1), cc k * ((n : ℤ) + 1 - k) +
          ∑ k ∈ Finset.range (n + 1 + 1), cc k := by
      rw [Finset.sum_range_succ _ (n + 1), Finset.sum_range_succ (fun k => cc k) (n + 1),
        ← add_assoc, ← Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl; intro k _; push_cast; ring
      · push_cast; ring
    rw [h1, ih, sum_cc]
    ring

/-- The doubling recursion `A_{n+2} = 2A_{n+1} + 2^{n+2} - 2`. -/
theorem Al_double (n : ℕ) : Al (n + 2) = 2 * Al (n + 1) + 2 ^ (n + 2) - 2 := by
  have h2 := Al_succ (n + 1)
  have h1 := Al_succ n
  rw [Finset.sum_range_succ] at h2
  have hd : ∑ k ∈ Finset.range (n + 1), (Al k + cc k * fA (n + 1 + 1 - k)) =
      Al (n + 1) + 2 * ∑ k ∈ Finset.range (n + 1), cc k * ((n : ℤ) + 1 - k) := by
    rw [h1, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [fA, fA, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [h2, hd, sum_cc_weighted, fA]
  simp
  ring

/-- **EK p. 40:** `A_n = 2 + 2ⁿ(n - 2)` for `n ≥ 1`. -/
theorem A_closed (n : ℕ) (hn : 1 ≤ n) : sumA n = 2 + 2 ^ n * ((n : ℤ) - 2) := by
  rw [sumA_eq]
  induction n, hn using Nat.le_induction with
  | base => rw [Al_succ 0]; simp [Al_zero, cc, fA]
  | succ n hn ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Al_double, ih]
    push_cast
    ring

/-- **EK p. 40, the recursion for `A_n`:**
`A_n = n(n-1) + Σ_{k=1}^{n-1} [2^{n-k-1} k(k-1) + A_{n-k}]` for `n ≥ 1`. -/
theorem A_recursion (n : ℕ) (hn : 1 ≤ n) :
    sumA n = (n : ℤ) * ((n : ℤ) - 1) +
      ∑ k ∈ Finset.Ico 1 n, (2 ^ (n - k - 1) * ((k : ℤ) * ((k : ℤ) - 1)) + sumA (n - k)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [sumA_eq]
  rw [Al_succ, Finset.sum_range_succ', Finset.sum_Ico_eq_sum_range, ← Finset.sum_range_reflect]
  rw [show m + 1 - 1 = m by omega, Al_zero, add_comm]
  congr 1
  · simp [cc, fA]
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [show m - 1 - j + 1 = m - j by omega, show m + 1 - (m - j) = j + 1 by omega,
      show m + 1 - (1 + j) - 1 = m - j - 1 by omega, show m + 1 - (1 + j) = m - j by omega, cc,
      fA]
    push_cast
    ring

/-- **EK (5.1), second equality** (doubled to stay in `ℤ`):
`2D = 2^{n-1} n(n-1) - A_n`. -/
theorem eq_5_1 (n : ℕ) : 2 * degD n = 2 ^ (n - 1) * ((n : ℤ) * ((n : ℤ) - 1)) - sumA n := by
  have hc : ∀ a : ℕ, 2 * (a.choose 2 : ℤ) = (a : ℤ) * ((a : ℤ) - 1) := by
    intro a
    have h := Nat.choose_two_right a
    have h2 : 2 * a.choose 2 = a * (a - 1) := by
      rw [h]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self a).two_dvd
    rcases a with _ | a
    · simp
    · have : ((2 * (a + 1).choose 2 : ℕ) : ℤ) = (((a + 1) * (a + 1 - 1) : ℕ) : ℤ) := by rw [h2]
      push_cast at this
      rw [this]; simp
  have hl : ∀ l : List ℕ, 2 * (l.map (fun a => (a.choose 2 : ℤ))).sum =
      (l.map (fun a : ℕ => (a : ℤ) * ((a : ℤ) - 1))).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, mul_add, ih, hc]
  rw [degD, sumA, Finset.mul_sum]
  rw [show (2 : ℤ) ^ (n - 1) * ((n : ℤ) * ((n : ℤ) - 1)) =
    ∑ _α : Composition n, (n : ℤ) * ((n : ℤ) - 1) by
      rw [Finset.sum_const, Finset.card_univ, composition_card, nsmul_eq_mul]; push_cast; ring]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [mul_sub, hc n, hl]

/-- **EK (5.2):** `D = 2^{n-2}(n² - 3n + 4) - 1` for `n ≥ 2`. -/
theorem eq_5_2 (n : ℕ) (hn : 2 ≤ n) :
    degD n = 2 ^ (n - 2) * ((n : ℤ) ^ 2 - 3 * n + 4) - 1 := by
  have h1 := eq_5_1 n
  rw [A_closed n (by omega)] at h1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega] at *
  have h2 : 2 * degD (m + 2) = 2 * (2 ^ m * (((m + 2 : ℕ) : ℤ) ^ 2 - 3 * ((m + 2 : ℕ) : ℤ) + 4) - 1) := by
    rw [h1]; push_cast; ring
  exact mul_left_cancel₀ two_ne_zero h2

end OddMath.Frontier.EKRest
