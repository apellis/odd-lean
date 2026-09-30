import OddMath.Frontier.EQZabSchur
import OddMath.Frontier.LongestReversal

/-!
# The hat odd Schur polynomials (Ellis–Qi, Lemma 4.5)

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, the definitions of `η^n_λ`, `s̃̂_λ`, `ŝ_λ` before Lemma 4.5, Lemma 4.5 and the formula after
it (printed numbering).

Rank `N`, strands numbered from `0`, `w₀` the plain permutation action (`longestPerm`),
`∂_{w₀} = LongestDivided.D N`. For an exponent vector `λ : Fin N → ℕ`:

* `etaHat λ = Σ_j λ_j binom(N-j, 2)` (Ellis–Qi's `η^n_λ = Σ_j λ_j binom(n-j+1, 2)` with `1`-based
  `j`);
* `hatExp λ = (λ_{N-1}, 1 + λ_{N-2}, …, N-1 + λ_0)`, the exponents of
  `x_1^{λ_n} ⋯ x_n^{n-1+λ_1}`;
* `twistedHat N λ = (-1)^{binom(N,3) + η} w₀ ∂_{w₀}(x^{hatExp λ})` (Ellis–Qi's `s̃̂_λ ∈ OΛ̃_N`;
  it is EKL's dual Schur polynomial of Definition 4.10, `ThickDots.dualSchur`, whose `w₀` is
  EKL's signed action);
* `untwistedHat N λ = (-1)^{binom(N,3) + η} θ w₀ ∂_{w₀}(x^{hatExp λ})` (Ellis–Qi's `ŝ_λ`).

Lemma 4.5 asserts the commutative square `s ↔ ŝ` (via `(-1)^{binom(n,3) + binom(n-1,2)|λ| +
Σ_{i<j} λ_i λ_j} w₀`), `s̃ ↔ s̃̂` (via `(-1)^{binom(n,3) + binom(n,2)|λ| + Σ_{i<j} λ_i λ_j} w₀`),
`s ↔ s̃` and `ŝ ↔ s̃̂` (via `θ`), and the text after it derives
`s̃̂_λ = (-1)^{Σ_{i<j} λ_i λ_j} ∂_{w₀}(x^λ x^δ)`.

* The vertical arrows hold (`untwistedHat_eq_theta`, and (3.27) `twisted_eq_theta_untwisted`).
* **The printed horizontal signs are wrong.** The correct statements (`twistedHat_eq_D`,
  `lemma_4_5_bottom`, `lemma_4_5_top`) carry the extra factor
  `(-1)^{binom(N+1,4) + Σ_j λ_j (N-1-j)}` (`hatCorr`):
  `s̃̂_λ = (-1)^{binom(N+1,4) + Σ_j λ_j (N-1-j) + Σ_{i<j} λ_i λ_j} ∂_{w₀}(x^λ x^δ)`, for every
  exponent vector `λ`. The factor is not identically `1`: already for `N = 2`, `λ = (1, 0)` the three
  printed identities fail (`lemma_4_5_bottom_false`, `lemma_4_5_top_false`, `hat_formula_false`).
-/

namespace OddMath.Frontier.EQZab

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open EQSkewDifferential EQSchur
open scoped BigOperators

noncomputable section

local instance (priority := high) zabHatNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) zabHatNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {N : ℕ}

/-! ## Definitions -/

/-- `η^N_λ = Σ_j λ_j binom(N - j, 2)` (`0`-based `j`). -/
def etaHat (l : Fin N → ℕ) : ℕ := ∑ j, l j * (N - j.val).choose 2

/-- The exponents of `x_1^{λ_N} x_2^{1+λ_{N-1}} ⋯ x_N^{N-1+λ_1}`. -/
def hatExp (l : Fin N → ℕ) : Fin N → ℕ := fun i => l (Fin.rev i) + i.val

/-- Ellis–Qi's `s̃̂_λ = (-1)^{binom(N,3) + η^N_λ} (w₀ ∘ ∂_{w₀})(x_1^{λ_N} ⋯ x_N^{N-1+λ_1})`. -/
def twistedHat (N : ℕ) (l : Fin N → ℕ) : SkewPolynomial N :=
  (-1 : ℤ) ^ (N.choose 3 + etaHat l) •
    longestPerm N (LongestDivided.D N (monomial (hatExp l) 1))

/-- Ellis–Qi's `ŝ_λ = (-1)^{binom(N,3) + η^N_λ} (θ ∘ w₀ ∘ ∂_{w₀})(x_1^{λ_N} ⋯ x_N^{N-1+λ_1})`. -/
def untwistedHat (N : ℕ) (l : Fin N → ℕ) : SkewPolynomial N :=
  (-1 : ℤ) ^ (N.choose 3 + etaHat l) •
    theta N (longestPerm N (LongestDivided.D N (monomial (hatExp l) 1)))

/-- `Σ_{i<j} λ_i λ_j`. -/
def pairSum (l : Fin N → ℕ) : ℕ := ∑ i, ∑ j, if i < j then l i * l j else 0

/-- `Σ_j λ_j (N - 1 - j) = Σ_j λ_j δ_j`. -/
def stairDot (l : Fin N → ℕ) : ℕ := ∑ j, l j * (N - 1 - j.val)

/-- The correction factor `(-1)^{binom(N+1,4) + Σ_j λ_j (N-1-j)}` missing from Lemma 4.5. -/
def hatCorr (N : ℕ) (l : Fin N → ℕ) : ℤ := (-1) ^ ((N+1).choose 4 + stairDot l)

/-- The right vertical arrow of Lemma 4.5: `ŝ_λ = θ(s̃̂_λ)`. -/
theorem untwistedHat_eq_theta (l : Fin N → ℕ) : untwistedHat N l = theta N (twistedHat N l) := by
  rw [untwistedHat, twistedHat, map_zsmul]

/-! ## Sign bookkeeping -/

theorem pairSum_rev (c : Fin N → ℕ) : pairSum (fun i => c (Fin.rev i)) = pairSum c := by
  unfold pairSum
  rw [← Equiv.sum_comp Fin.revPerm]
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  have e : ∀ i : Fin N, (∑ j, if Fin.rev i < j then c i * c (Fin.rev j) else 0) =
      ∑ j, if j < i then c i * c j else 0 := fun i => by
    rw [← Equiv.sum_comp Fin.revPerm]
    simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.rev_lt_rev]
  rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem pairSum_add (a b : Fin N → ℕ) :
    pairSum (a + b) = pairSum a + pairSum b +
      (OddMath.crossingCount b a + OddMath.crossingCount a b) := by
  have e : ∀ i j : Fin N, (if i < j then (a + b) i * (a + b) j else 0) =
      (if i < j then a i * a j else 0) + (if i < j then b i * b j else 0) +
        ((if i < j then a i * b j else 0) + (if i < j then b i * a j else 0)) := by
    intro i j; split_ifs
    · simp only [Pi.add_apply]; ring
    · simp
  unfold pairSum
  simp only [e, Finset.sum_add_distrib]
  congr 2
  · unfold OddMath.crossingCount
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  · unfold OddMath.crossingCount
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring

theorem choose_two_succ (m : ℕ) : (m+1).choose 2 = m.choose 2 + m := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

theorem range_sum_add_choose (k : ℕ) (hk : k ≤ N) :
    ∑ t ∈ Finset.range k, (N - 1 - t) + (N - k).choose 2 = N.choose 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h := ih (by omega)
    have hc : (N - k).choose 2 = (N - (k+1)).choose 2 + (N - (k+1)) := by
      rw [show N - k = (N - (k+1)) + 1 by omega, choose_two_succ]
    omega

theorem sum_lt_delta_add_choose (i : Fin N) :
    ∑ j ∈ Finset.univ.filter (· < i), delta N j + (N - i.val).choose 2 = N.choose 2 := by
  have e : ∑ j ∈ Finset.univ.filter (· < i), delta N j = ∑ t ∈ Finset.range i.val, (N - 1 - t) := by
    rw [Finset.sum_filter]
    simp only [Fin.lt_def, delta]
    rw [Fin.sum_univ_eq_sum_range (fun t => if t < i.val then N - 1 - t else 0) N,
      ← Finset.sum_filter]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    have := i.isLt
    omega
  rw [e, range_sum_add_choose _ i.isLt.le]

theorem crossingCount_delta_add_eta (l : Fin N → ℕ) :
    OddMath.crossingCount l (delta N) + etaHat l = (∑ j, l j) * N.choose 2 := by
  unfold OddMath.crossingCount etaHat
  rw [← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, ← mul_add, sum_lt_delta_add_choose]

theorem sum_hatExp (l : Fin N → ℕ) : ∑ j, hatExp l j = N.choose 2 + ∑ j, l j := by
  unfold hatExp
  rw [Finset.sum_add_distrib, add_comm]
  congr 1
  · rw [Fin.sum_univ_eq_sum_range (fun t => t), Finset.sum_range_id, Nat.choose_two_right]
  · exact Equiv.sum_comp Fin.revPerm l

theorem hatExp_rev (l : Fin N → ℕ) : (fun j => hatExp l (Fin.rev j)) = l + delta N := by
  funext j
  simp only [hatExp, Fin.rev_rev, Pi.add_apply, delta, Fin.val_rev]
  omega

/-- The parity bookkeeping of the corrected Lemma 4.5. -/
theorem hat_sign_even (l : Fin N → ℕ) :
    Even ((N.choose 3 + etaHat l) + N.choose 2 * ∑ j, l j + N.choose 2 +
        (N.choose 2 * ∑ j, hatExp l j + pairSum (hatExp l)) +
      ((N+1).choose 4 + stairDot l + pairSum l + OddMath.crossingCount l (delta N))) := by
  have F1 : pairSum (hatExp l) = pairSum (l + delta N) := by
    rw [← pairSum_rev (hatExp l), hatExp_rev]
  have F2 := pairSum_add l (delta N)
  have F3 := crossingCount_add_swap l (delta N)
  rw [sum_delta] at F3
  have F4 := crossingCount_delta_add_eta l
  obtain ⟨k5, F5⟩ := MonomialReversal.even_pairSum_add_choose_four N
  have F5' : pairSum (delta N) + N.choose 4 = k5 + k5 := F5
  have F6 : (N+1).choose 4 = N.choose 3 + N.choose 4 := Nat.choose_succ_succ' N 3
  obtain ⟨k7, F7⟩ := Nat.even_mul_succ_self (N.choose 2)
  rw [sum_hatExp, F1, F2, F6]
  have hsd : stairDot l = ∑ j, l j * delta N j := rfl
  rw [hsd]
  generalize N.choose 2 = C2 at *
  generalize N.choose 3 = C3 at *
  generalize N.choose 4 = C4 at *
  generalize ∑ j, l j = L at *
  generalize ∑ j, l j * delta N j = S at *
  generalize etaHat l = E at *
  generalize pairSum l = P at *
  generalize pairSum (delta N) = Q at *
  generalize OddMath.crossingCount l (delta N) = X at *
  generalize OddMath.crossingCount (delta N) l = Y at *
  refine ⟨k5 + k7 + C3 + 2 * (C2 * L) + P, ?_⟩
  have h1 : C2 * (C2 + L) = C2 * C2 + C2 * L := by ring
  have h2 : L * C2 = C2 * L := by ring
  have h3 : C2 * (C2 + 1) = C2 * C2 + C2 := by ring
  rw [h1]
  rw [h2] at F3 F4
  rw [h3] at F7
  generalize C2 * L = M at *
  generalize C2 * C2 = SQ at *
  omega

/-! ## The corrected Lemma 4.5 -/

/-- The formula after Lemma 4.5, **corrected**: for every exponent vector `λ`,
`s̃̂_λ = (-1)^{binom(N+1,4) + Σ_j λ_j (N-1-j)} (-1)^{Σ_{i<j} λ_i λ_j} ∂_{w₀}(x^λ x^δ)`.
(Ellis–Qi print it without the factor `hatCorr N λ = (-1)^{binom(N+1,4) + Σ_j λ_j (N-1-j)}`.) -/
theorem twistedHat_eq_D (l : Fin N → ℕ) :
    twistedHat N l = (hatCorr N l * (-1) ^ pairSum l) •
      LongestDivided.D N (monomial l 1 * LongestDivided.staircase N) := by
  open SignedPermutation LongestElementary in
  have hpar : parityInv N (monomial (hatExp l) 1) =
      (-1 : ℤ) ^ (N.choose 2 + ∑ j, l j) • monomial (hatExp l) 1 := by
    rw [parityInv_monomial, sum_hatExp]
  have hD := parityInv_D_of l _ hpar
  open SignedPermutation LongestElementary in
  have hw := skewAction_longest _ _ hD
  open SignedPermutation LongestElementary in
  have hw' : longestPerm N (LongestDivided.D N (monomial (hatExp l) 1)) =
      (-1 : ℤ) ^ (N.choose 2 * ∑ j, l j) •
        skewAction (longest N) (LongestDivided.D N (monomial (hatExp l) 1)) := by
    rw [hw, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  rw [twistedHat, hw', LongestReversal.action_D, MonomialReversal.longest_monomial,
    hatExp_rev, staircase_eq_monomial, OddSchurPieri.mono_mul]
  simp only [map_zsmul, smul_smul]
  congr 1
  rw [hatCorr, OddMath.skewSign]
  have key := MonomialReversal.neg_one_pow_of_even_add (hat_sign_even l)
  simp only [← pow_add]
  convert key using 2
  unfold pairSum
  ring

/-- **Lemma 4.5, bottom arrow, corrected**: `s̃̂_λ = hatCorr N λ · (-1)^{binom(N,3) + binom(N,2)|λ| +
Σ_{i<j} λ_i λ_j} w₀(s̃_λ)`. -/
theorem lemma_4_5_bottom (l : Fin N → ℕ) :
    twistedHat N l = (hatCorr N l *
      (-1) ^ (N.choose 3 + N.choose 2 * ∑ j, l j + pairSum l)) • longestPerm N (twisted N l) := by
  rw [twistedHat_eq_D, twisted, map_zsmul, longestPerm_longestPerm, smul_smul]
  congr 1
  rw [pow_add (-1 : ℤ) (N.choose 3 + N.choose 2 * ∑ j, l j) (pairSum l)]
  have : ((-1 : ℤ) ^ (N.choose 3 + N.choose 2 * ∑ j, l j)) *
      (-1) ^ (N.choose 3 + N.choose 2 * ∑ j, l j) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  linear_combination (-(hatCorr N l * (-1) ^ pairSum l)) * this

/-- **Lemma 4.5, top arrow, corrected**: `ŝ_λ = hatCorr N λ · (-1)^{binom(N,3) + binom(N-1,2)|λ| +
Σ_{i<j} λ_i λ_j} w₀(s_λ)`. -/
theorem lemma_4_5_top (l : Fin N → ℕ) :
    untwistedHat N l = (hatCorr N l *
      (-1) ^ (N.choose 3 + (N-1).choose 2 * ∑ j, l j + pairSum l)) •
        longestPerm N (untwisted N l) := by
  rw [untwistedHat_eq_theta, lemma_4_5_bottom, map_zsmul,
    theta_longestPerm _ _ (parityInv_twisted l), ← untwisted_eq_theta_twisted, smul_smul]
  congr 1
  rw [mul_assoc]
  congr 1
  rw [← pow_add]
  apply MonomialReversal.neg_one_pow_of_even_add
  rcases N with _ | N
  · simp
  · have hc : (N+1).choose 2 = N.choose 2 + N := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    rw [hc, show N + 1 - 1 = N by omega]
    generalize ∑ j, l j = L
    refine ⟨(N+1).choose 3 + N.choose 2 * L + pairSum l + L + N * L, ?_⟩
    ring

/-! ## The printed signs are wrong -/

theorem twisted_two_one : longestPerm 2 (twisted 2 ![1, 0]) = generator 1 - generator 0 := by
  rw [twisted_one_eq, map_sub, longestPerm_generator, longestPerm_generator]
  rfl

theorem generator_sub_ne_zero : (generator 1 - generator 0 : SkewPolynomial 2) ≠ 0 := by
  intro h
  have hne : (expSingle (0 : Fin 2) : Fin 2 → ℕ) ≠ expSingle 1 := by
    intro e
    have := congrFun e 0
    simp [expSingle] at this
  have := congrArg (fun f : SkewPolynomial 2 => f (expSingle 1)) h
  simp [OddMath.SkewPolynomial.generator, OddMath.SkewPolynomial.monomial,
    Finsupp.sub_apply, hne] at this

theorem hatCorr_two : hatCorr 2 ![1, 0] = -1 := by
  simp [hatCorr, stairDot, Fin.sum_univ_two]

/-- The bottom arrow of Lemma 4.5 as printed is false (`N = 2`, `λ = (1, 0)`). -/
theorem lemma_4_5_bottom_false :
    ¬ ∀ (N : ℕ) (l : Fin N → ℕ), Antitone l →
      twistedHat N l =
        ((-1 : ℤ) ^ (N.choose 3 + N.choose 2 * ∑ j, l j + pairSum l)) • longestPerm N (twisted N l) := by
  intro h
  have h1 := h 2 ![1, 0] (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
  rw [lemma_4_5_bottom, hatCorr_two, neg_one_mul, neg_smul, neg_eq_iff_add_eq_zero, ← two_smul ℤ,
    smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · norm_num at h1
  · rw [smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (pow_ne_zero _ (by norm_num))
    · rw [twisted_two_one] at h1
      exact generator_sub_ne_zero h1

/-- The top arrow of Lemma 4.5 as printed is false (`N = 2`, `λ = (1, 0)`). -/
theorem lemma_4_5_top_false :
    ¬ ∀ (N : ℕ) (l : Fin N → ℕ), Antitone l →
      untwistedHat N l =
        ((-1 : ℤ) ^ (N.choose 3 + (N-1).choose 2 * ∑ j, l j + pairSum l)) •
          longestPerm N (untwisted N l) := by
  intro h
  apply lemma_4_5_bottom_false
  intro N l hl
  have h1 : twistedHat N l = theta N (untwistedHat N l) := by
    rw [untwistedHat_eq_theta, theta_theta]
  rw [h1, h N l hl, map_zsmul, theta_longestPerm _ _ (parityInv_untwisted l),
    ← twisted_eq_theta_untwisted, smul_smul, ← pow_add]
  congr 1
  apply MonomialReversal.neg_one_pow_of_even_add
  rcases N with _ | N
  · simp
  · have hc : (N+1).choose 2 = N.choose 2 + N := choose_two_succ N
    rw [hc, show N + 1 - 1 = N by omega]
    generalize ∑ j, l j = L
    refine ⟨(N+1).choose 3 + N.choose 2 * L + pairSum l + L + N * L, ?_⟩
    ring

/-- The formula after Lemma 4.5 as printed, `s̃̂_λ = (-1)^{Σ_{i<j} λ_i λ_j} ∂_{w₀}(x^λ x^δ)`, is
false (`N = 2`, `λ = (1, 0)`). -/
theorem hat_formula_false :
    ¬ ∀ (N : ℕ) (l : Fin N → ℕ), Antitone l →
      twistedHat N l =
        ((-1 : ℤ) ^ pairSum l) • LongestDivided.D N (monomial l 1 * LongestDivided.staircase N) := by
  intro h
  apply lemma_4_5_bottom_false
  intro N l hl
  rw [h N l hl, twisted, map_zsmul, longestPerm_longestPerm, smul_smul]
  congr 1
  rw [pow_add (-1 : ℤ) (N.choose 3 + N.choose 2 * ∑ j, l j) (pairSum l)]
  have : ((-1 : ℤ) ^ (N.choose 3 + N.choose 2 * ∑ j, l j)) *
      (-1) ^ (N.choose 3 + N.choose 2 * ∑ j, l j) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  linear_combination (-((-1 : ℤ) ^ pairSum l)) * this

end

end OddMath.Frontier.EQZab
