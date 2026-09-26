import Mathlib.RingTheory.LaurentSeries
import OddMath.Frontier.EKLSectionTwoE
import OddMath.Frontier.EKLSectionTwoH

/-! # EKL: displays of §2 and §3.2 (misprints and unnumbered claims)

EKL = Ellis–Khovanov–Lauda, *The odd nilHecke algebra and its diagrammatics*,
arXiv:1111.1320v1.

* (2.18), p. 6: the middle expression, with denominator `q^a - q^{-a}`, is false at `a = 2`
  (`eq_2_18_printed_false`); with `q^i - q^{-i}` all three expressions agree for every `a`
  (`eq_2_18`). Stated in the field `ℚ((q))` of Laurent series. The outer equality for `OΛ_a` is
  `EKLSectionTwo.qrk_symmetric`.
* (2.43), p. 11: the printed selector `w = u⁻¹` holds for `a = 2` (`printed_2_43_rank_two`) and
  fails for every `a ≥ 3` (`printed_2_43_false`); the correct selector is `w = u` (`eq_2_43`).
* Proof of (2.51), p. 12: the step `h x_{a-1}^i ∈ H_{a-1}` (`h ∈ H_{a-2}`) is false for `H` of
  (2.46) (`eq_2_51_step_false`).
* Remark 2.17, p. 14: `s_1(ε_1(x̃_1, x̃_2, x̃_3)) = x̃_2 + x̃_1 - x̃_3` (`remark_2_17`).
* (3.14), p. 22: the middle expression `Σ_{j=1}^{a-2} Σ_{ℓ=1}^{j} j` is false at `a = 4`
  (`eq_3_14_printed_false`); with `Σ_ℓ ℓ` the identity holds for every `a` (`eq_3_14`).
-/

namespace OddMath.Frontier.EKLGaps
open HahnSeries
open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open NilCoxeterWords OddSchubertAction FiniteCompleteElementary
open scoped BigOperators
noncomputable section

/-! ### (2.18) -/

/-- Laurent series in `q` over `ℚ`, a field. -/
abbrev QL := LaurentSeries ℚ

/-- The variable `q`. -/
def qL : QL := single 1 1

theorem qL_pow_eq_single (m : ℕ) : qL ^ m = single (m : ℤ) 1 := by
  rw [qL, single_pow, one_pow, nsmul_eq_mul, mul_one]

theorem qL_ne_zero : qL ≠ 0 := by
  rw [qL]; exact single_ne_zero one_ne_zero

theorem qL_inv : qL⁻¹ = single (-1) 1 := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [qL, single_mul_single, add_neg_cancel, mul_one]; rfl

theorem qL_pow_ne_one {m : ℕ} (hm : m ≠ 0) : qL ^ m ≠ 1 := by
  rw [qL_pow_eq_single]
  intro h
  have := congrArg (fun f : QL => f.coeff 0) h
  simp only at this
  rw [HahnSeries.coeff_single_of_ne (by exact_mod_cast (Ne.symm hm))] at this
  simp at this

theorem one_sub_qL_pow_ne_zero {m : ℕ} (hm : m ≠ 0) : 1 - qL ^ m ≠ 0 :=
  sub_ne_zero.mpr (qL_pow_ne_one hm).symm

theorem qL_mul_inv : qL * qL⁻¹ = 1 := mul_inv_cancel₀ qL_ne_zero

theorem qL_pow_sub_inv_pow (m : ℕ) : qL ^ m - qL⁻¹ ^ m = (qL ^ (2*m) - 1) * qL⁻¹ ^ m := by
  rw [sub_mul, one_mul, two_mul, pow_add, mul_assoc, ← mul_pow, qL_mul_inv, one_pow, mul_one]

theorem qL_sub_inv : qL - qL⁻¹ = (qL ^ 2 - 1) * qL⁻¹ := by
  simpa using qL_pow_sub_inv_pow 1

theorem qL_pow_sub_inv_pow_ne_zero {m : ℕ} (hm : m ≠ 0) : qL ^ m - qL⁻¹ ^ m ≠ 0 := by
  rw [qL_pow_sub_inv_pow]
  exact mul_ne_zero (sub_ne_zero.mpr (qL_pow_ne_one (by omega)))
    (pow_ne_zero _ (inv_ne_zero qL_ne_zero))

/-- EKL (2.18), first line: `∏_{i=1}^{a} 1/(1-q^{2i})`. -/
def rank218First (a : ℕ) : QL := ∏ i ∈ Finset.range a, (1 - qL ^ (2*(i+1)))⁻¹

/-- EKL (2.18), middle expression as printed:
`(1-q²)^{-a} ∏_{i=1}^{a} q^{-i+1}(q-q^{-1})/(q^a-q^{-a})` (the product index `i` runs over
`1, …, a`; here `i = j+1`, `j ∈ range a`). -/
def rank218MiddlePrinted (a : ℕ) : QL :=
  ((1 - qL^2)^a)⁻¹ * ∏ i ∈ Finset.range a, (qL⁻¹ ^ i * (qL - qL⁻¹) / (qL ^ a - qL⁻¹ ^ a))

/-- EKL (2.18), middle expression corrected:
`(1-q²)^{-a} ∏_{i=1}^{a} q^{-i+1}(q-q^{-1})/(q^i-q^{-i})`. -/
def rank218Middle (a : ℕ) : QL :=
  ((1 - qL^2)^a)⁻¹ * ∏ i ∈ Finset.range a, (qL⁻¹ ^ i * (qL - qL⁻¹) / (qL ^ (i+1) - qL⁻¹ ^ (i+1)))

theorem rank218_factor (i : ℕ) :
    (1 - qL ^ (2*(i+1)))⁻¹ = (1 - qL^2)⁻¹ * (qL⁻¹ ^ i * (qL - qL⁻¹) / (qL ^ (i+1) - qL⁻¹ ^ (i+1))) := by
  have h1 : qL ^ (2*(i+1)) - 1 ≠ 0 := sub_ne_zero.mpr (qL_pow_ne_one (by omega))
  have h2 : 1 - qL ^ 2 ≠ 0 := one_sub_qL_pow_ne_zero (by omega)
  have hu : qL⁻¹ ≠ 0 := inv_ne_zero qL_ne_zero
  rw [qL_pow_sub_inv_pow, qL_sub_inv]
  generalize qL⁻¹ = u at hu ⊢
  generalize qL ^ (2*(i+1)) = Q at h1 ⊢
  have h1' : 1 - Q ≠ 0 := fun h => h1 (by linear_combination -h)
  field_simp
  ring


theorem rank218First_eq_middle (a : ℕ) : rank218First a = rank218Middle a := by
  rw [rank218First, rank218Middle, Finset.prod_congr rfl (fun i _ => rank218_factor i), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_range, inv_pow]

theorem prod_qL_inv_pow (a : ℕ) : ∏ i ∈ Finset.range a, qL⁻¹ ^ i = qL⁻¹ ^ a.choose 2 := by
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id, Nat.choose_two_right]

/-- The balanced `q`-integer `[m] = (q^m - q^{-m})/(q - q^{-1})` of EKL (2.15). -/
def qintL (m : ℕ) : QL := (qL ^ m - qL⁻¹ ^ m) / (qL - qL⁻¹)

/-- The balanced `q`-factorial `[a]! = [a][a-1]⋯[1]` of EKL (2.15). -/
def qfactL (a : ℕ) : QL := ∏ i ∈ Finset.range a, qintL (i+1)

theorem rank218Middle_eq (a : ℕ) :
    rank218Middle a = qL⁻¹ ^ a.choose 2 * (qfactL a)⁻¹ * ((1 - qL^2)^a)⁻¹ := by
  have hd : qL - qL⁻¹ ≠ 0 := by simpa using qL_pow_sub_inv_pow_ne_zero (m := 1) one_ne_zero
  have hterm : ∀ i ∈ Finset.range a, qL⁻¹ ^ i * (qL - qL⁻¹) / (qL ^ (i+1) - qL⁻¹ ^ (i+1)) =
      qL⁻¹ ^ i * (qintL (i+1))⁻¹ := by
    intro i _
    have h := qL_pow_sub_inv_pow_ne_zero (m := i+1) (by omega)
    rw [qintL, inv_div]
    field_simp
  rw [rank218Middle, Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, prod_qL_inv_pow, qfactL,
    Finset.prod_inv_distrib]
  ring

theorem rank218First_ne_zero (a : ℕ) : rank218First a ≠ 0 := by
  rw [rank218First, Finset.prod_ne_zero_iff]
  intro i _
  exact inv_ne_zero (one_sub_qL_pow_ne_zero (by omega))

theorem qL_add_inv_ne_one : qL + qL⁻¹ ≠ 1 := by
  intro h
  rw [qL_inv] at h
  have := congrArg (fun f : QL => f.coeff 0) h
  simp only [qL, HahnSeries.coeff_add] at this
  rw [HahnSeries.coeff_single_of_ne (by norm_num), HahnSeries.coeff_single_of_ne (by norm_num)]
    at this
  simp at this

theorem rank218MiddlePrinted_two :
    rank218MiddlePrinted 2 = rank218Middle 2 * ((qL - qL⁻¹) / (qL ^ 2 - qL⁻¹ ^ 2)) := by
  have h1 := qL_pow_sub_inv_pow_ne_zero (m := 1) one_ne_zero
  have h2 := qL_pow_sub_inv_pow_ne_zero (m := 2) two_ne_zero
  simp only [pow_one] at h1
  simp only [rank218MiddlePrinted, rank218Middle, Finset.prod_range_succ, Finset.prod_range_zero,
    one_mul, pow_zero, zero_add, pow_one]
  field_simp
  ring

/-- **EKL (2.18), middle expression, as printed, is false**: at `a = 2`,
`∏_{i=1}^{a} 1/(1-q^{2i}) ≠ (1-q²)^{-a} ∏_{i=1}^{a} q^{-i+1}(q-q^{-1})/(q^a-q^{-a})`
in the field of Laurent series `ℚ((q))`. The two sides differ by the factor `q + q^{-1}`. -/
theorem eq_2_18_printed_false : rank218First 2 ≠ rank218MiddlePrinted 2 := by
  intro h
  have h1 := qL_pow_sub_inv_pow_ne_zero (m := 1) one_ne_zero
  have h2 := qL_pow_sub_inv_pow_ne_zero (m := 2) two_ne_zero
  simp only [pow_one] at h1
  rw [rank218MiddlePrinted_two, ← rank218First_eq_middle] at h
  have hr : (qL - qL⁻¹) / (qL ^ 2 - qL⁻¹ ^ 2) = 1 := by
    exact (mul_left_cancel₀ (rank218First_ne_zero 2) (h.symm.trans (mul_one _).symm))
  rw [div_eq_one_iff_eq h2] at hr
  apply qL_add_inv_ne_one
  have hf : (qL - qL⁻¹) * (qL + qL⁻¹ - 1) = 0 := by linear_combination -hr
  rcases mul_eq_zero.mp hf with h0 | h0
  · exact absurd h0 h1
  · exact sub_eq_zero.mp h0

theorem eq_2_18_printed_false' : ¬ ∀ a : ℕ, rank218First a = rank218MiddlePrinted a :=
  fun h => eq_2_18_printed_false (h 2)

/-- **EKL (2.18), corrected**, in `ℚ((q))`, for every `a`:
`∏_{i=1}^{a} 1/(1-q^{2i}) = (1-q²)^{-a} ∏_{i=1}^{a} q^{-i+1}(q-q^{-1})/(q^i-q^{-i})
= q^{-a(a-1)/2} ([a]!)^{-1} (1-q²)^{-a}`, with `[a]!` the balanced `q`-factorial (2.15). -/
theorem eq_2_18 (a : ℕ) :
    rank218First a = rank218Middle a ∧
      rank218Middle a = qL⁻¹ ^ a.choose 2 * (qfactL a)⁻¹ * ((1 - qL^2)^a)⁻¹ :=
  ⟨rank218First_eq_middle a, rank218Middle_eq a⟩

/-! ### (3.14) -/

theorem sum_Icc_id (j : ℕ) : ∑ ℓ ∈ Finset.Icc 1 j, ℓ = (j+1).choose 2 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.choose_succ_succ' (j+1), Nat.choose_one_right]
    ring

theorem sum_Icc_choose (m : ℕ) : ∑ j ∈ Finset.Icc 1 m, (j+1).choose 2 = (m+2).choose 3 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.choose_succ_succ' (m+2) 2]
    ring

theorem sum_Icc_choose_two (m : ℕ) : ∑ j ∈ Finset.Icc 1 m, j.choose 2 = (m+1).choose 3 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.choose_succ_succ' (m+1) 2]
    ring

/-- **EKL (3.14), middle expression, as printed, is false** at `a = 4`:
`C(4,3) = 4`, while `Σ_{j=1}^{2} Σ_{ℓ=1}^{j} j = 1 + 2·2 = 5`. -/
theorem eq_3_14_printed_false :
    ¬ ∀ a : ℕ, a.choose 3 = ∑ j ∈ Finset.Icc 1 (a-2), ∑ _ℓ ∈ Finset.Icc 1 j, j := by
  intro h
  have := h 4
  revert this
  decide

/-- **EKL (3.14), corrected**, for every `a`:
`C(a,3) = Σ_{j=1}^{a-1} C(j,2) = Σ_{j=1}^{a-2} Σ_{ℓ=1}^{j} ℓ`. -/
theorem eq_3_14 (a : ℕ) :
    a.choose 3 = ∑ j ∈ Finset.Icc 1 (a-1), j.choose 2 ∧
      a.choose 3 = ∑ j ∈ Finset.Icc 1 (a-2), ∑ ℓ ∈ Finset.Icc 1 j, ℓ := by
  have h2 : a.choose 3 = ∑ j ∈ Finset.Icc 1 (a-2), ∑ ℓ ∈ Finset.Icc 1 j, ℓ := by
    simp only [sum_Icc_id]
    rcases Nat.lt_or_ge a 2 with ha | ha
    · interval_cases a <;> rfl
    · rw [sum_Icc_choose, Nat.sub_add_cancel ha]
  refine ⟨?_, h2⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; rfl
  · rw [sum_Icc_choose_two, Nat.sub_add_cancel ha]

/-! ### Remark 2.17 -/

open PlacticEvaluation (tildeGenerator) in
/-- **EKL Remark 2.17, the displayed value** (`a = 3`):
`s_1(ε_1(x̃_1, x̃_2, x̃_3)) = x̃_2 + x̃_1 - x̃_3` (0-based indices in Lean). -/
theorem remark_2_17 :
    AllRankDivided.s (0 : Fin 2) (elementaryPoly 3 1) =
      tildeGenerator (1 : Fin 3) + tildeGenerator 0 - tildeGenerator 2 := by
  rw [EKLSectionTwo.elementary_one_eq, map_sum, Fin.sum_univ_three]
  simp only [tildeGenerator, map_zsmul, AllRankDivided.s_generator]
  simp [Equiv.swap_apply_def, Fin.ext_iff]
  abel

/-! ### (2.43) -/

/-- The printed (2.43), second line: for `ℓ(w) = ℓ(u)`, `(x^A ∂_u)(s_w) = ± x^A` if `w = u⁻¹` and
`0` otherwise (rank `a = n+2`). -/
def Printed_2_43 (n : ℕ) : Prop :=
  ∀ (A : Fin (n+2) → ℕ) (u w : Perm n), length w = length u →
    (w = u⁻¹ → Signed (monomial A 1 * dividedElementOperator u (schubert w)) (monomial A 1)) ∧
    (w ≠ u⁻¹ → monomial A 1 * dividedElementOperator u (schubert w) = 0)

/-- **EKL (2.43), corrected**: for `ℓ(w) = ℓ(u)`, `(x^A ∂_u)(s_w) = ± x^A` if `w = u` and `0`
otherwise, in every rank `a = n+2`. -/
theorem eq_2_43 (n : ℕ) (A : Fin (n+2) → ℕ) (u w : Perm n) (hl : length w = length u) :
    (w = u → Signed (monomial A 1 * dividedElementOperator u (schubert w)) (monomial A 1)) ∧
    (w ≠ u → monomial A 1 * dividedElementOperator u (schubert w) = 0) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    rcases action_self w with h | h <;> rw [h]
    · exact Or.inl (mul_one _)
    · exact Or.inr (by rw [mul_neg, mul_one])
  · rw [action_same_length_distinct u w hl h, mul_zero]

theorem perm_two_inv (u : Perm 0) : u⁻¹ = u := by
  revert u; decide

/-- The printed (2.43) holds for `a = 2`: every permutation of `S_2` is an involution. -/
theorem printed_2_43_rank_two : Printed_2_43 0 := by
  intro A u w hl
  rw [perm_two_inv]
  exact eq_2_43 0 A u w hl

theorem three_cycle_ne_inv (n : ℕ) :
    (simple (n := n+1) 0 * simple 1)⁻¹ ≠ simple (n := n+1) 0 * simple 1 := by
  intro h
  have h2 : (simple (n := n+1) 0 * simple 1) * (simple 0 * simple 1) = 1 := by
    calc _ = (simple (n := n+1) 0 * simple 1)⁻¹ * (simple 0 * simple 1) := by rw [h]
      _ = 1 := inv_mul_cancel _
  have := congrArg (fun p : Perm (n+1) => (p 0).val) h2
  simp [simple, Equiv.swap_apply_def, Fin.ext_iff] at this

/-- **The printed (2.43) is false for every `a ≥ 3`**: for the 3-cycle `u = s_1 s_2` one has
`u ≠ u⁻¹`, and `∂_u(s_u) = ±1 ≠ 0`. -/
theorem printed_2_43_false (n : ℕ) : ¬ Printed_2_43 (n+1) := by
  intro h
  set u := simple (n := n+1) 0 * simple 1
  have h0 := (h 0 u u rfl).2 (fun e => three_cycle_ne_inv n e.symm)
  have hm : (monomial (0 : Fin (n+3) → ℕ) 1 : SkewPolynomial (n+3)) = 1 := rfl
  rw [hm, one_mul] at h0
  rcases action_self u with e | e <;> rw [e] at h0
  · exact one_ne_zero h0
  · exact one_ne_zero (neg_eq_zero.mp h0)

/-! ### The step in the proof of (2.51) -/

theorem pow_last_not_mem_H (N i : ℕ) (hi : 1 ≤ i) :
    generator (Fin.last N) ^ i ∉ SchubertBasis.H (N+1) := by
  rw [SchubertBasis.H_eq_box, SchubertBasis.mem_box, PbwL4.pow_form]
  intro h
  have := h (i • expSingle (Fin.last N)) (by simp [monomial]) (Fin.last N)
  simp [expSingle] at this
  omega

/-- **The step "h·x_{a-1}^i ∈ H_{a-1}" in the proof of (2.51) is false** for `H` of (2.46), for every
`a = N+3 ≥ 3`: `h = 1 ∈ H_{a-2}` and `i = 1` give `x_{a-1} ∉ H_{a-1}`. (Here `H_{a-2}` sits in
`OPol_{a-1}` via the first `a-2` variables.) -/
theorem eq_2_51_step_false (N : ℕ) :
    ¬ ∀ h ∈ SchubertBasis.H (N+1), ∀ i : ℕ, 1 ≤ i → i ≤ N+1 →
      ElementaryBranching.prefix (N+1) h * generator (Fin.last (N+1)) ^ i ∈ SchubertBasis.H (N+2) := by
  intro H
  have h1 : (1 : SkewPolynomial (N+1)) ∈ SchubertBasis.H (N+1) := by
    rw [SchubertBasis.H_eq_box]
    exact SchubertBasis.monomial_mem_box 0 _ 1 (fun _ => Nat.zero_le _)
  have := H 1 h1 1 le_rfl (by omega)
  rw [map_one, one_mul] at this
  exact pow_last_not_mem_H (N+1) 1 le_rfl this

end
end OddMath.Frontier.EKLGaps
