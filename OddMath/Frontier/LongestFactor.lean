import OddMath.Frontier.NilHeckeGradedEnd

/-! # Factorizations and degree bounds for the longest divided difference

EKL arXiv:1111.1320v1 (2.36)–(2.37), (3.11).

The longest odd divided difference `D N` is the literal source word (2.36) acting on the
genuine all-rank operators.  This module records three structural facts used in the
staircase evaluations:

* `D_factor_first`: for every simple index `i`, `D (n+2) = ε • (L ∘ ∂_i)` with `ε = ±1`,
  i.e. `∂_i` may be taken to act first.  The longest permutation has a right descent at
  every index, and reduced words of one permutation agree up to one global sign.
* `D_factor_right_peel`, `D_factor_left_peel`: in rank `n+3`, `D` equals, up to one global
  sign, the rank-`(n+2)` word on the first (resp. last) `n+2` variables followed by the
  written sweep `∂_0 ∂_1 ⋯ ∂_{n+1}` (resp. `∂_{n+1} ⋯ ∂_1 ∂_0`).  The concatenated words
  are shown to be reduced by exhibiting an explicit polynomial on which they act by `±1`.
* Degree bounds: every word of length `ℓ` lowers the polynomial degree by `ℓ`
  (`deg x_j = 2`), so `D N` kills monomials of degree below `C(N,2)` and sends monomials of
  degree `C(N,2)` to constants.

Written words compose as a right fold: the last letter of a list acts first.
-/
namespace OddMath.Frontier.LongestFactor
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open LongestDivided NilCoxeterWords NilHeckeGradedEnd
open scoped BigOperators

/-! ## Comparison with the source word -/

theorem length_longest (n : ℕ) :
    length (LongestElementary.longest (n+2)) = (n+2).choose 2 := by
  rw [← sourceWord_permutation n, ← sourceWord_reduced n, sourceWord_length]

/-- Any reduced word of maximal length expresses `D (n+2)` up to one global sign. -/
theorem D_eq_sign_of_reduced {n : ℕ} (w : Word n) (hw : Reduced w)
    (hl : w.length = (n+2).choose 2) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ D (n+2) = ε • applyWord w := by
  have hp : permutation w = LongestElementary.longest (n+2) :=
    eq_longest_of_length _ (hw.symm.trans hl)
  obtain ⟨ε, hε, -, h⟩ := reduced_global_sign (wordIn n (n+2) le_rfl) w
    (sourceWord_reduced n) hw ((sourceWord_permutation n).trans hp.symm)
  exact ⟨ε, hε, h⟩

/-- A word acting nontrivially on some polynomial is reduced. -/
theorem reduced_of_apply_ne {n : ℕ} (w : Word n) (f : SkewPolynomial (n+2))
    (hf : applyWord w f ≠ 0) : Reduced w := by
  by_contra h
  apply hf
  rw [nonreduced_operator_zero w h, LinearMap.zero_apply]

/-! ## First-crossing factorization -/

/-- The longest permutation has a right descent at every simple index. -/
theorem longest_descent (n : ℕ) (i : Fin (n+1)) :
    Descent (LongestElementary.longest (n+2)) i := by
  unfold Descent
  simp only [LongestElementary.longest_apply]
  exact Fin.rev_lt_rev.mpr (Fin.castSucc_lt_succ i)

/-- A reduced expression of the longest permutation ending with any prescribed letter. -/
theorem exists_reduced_ending (n : ℕ) (i : Fin (n+1)) :
    ∃ w : Word n, Reduced (w ++ [i]) ∧ (w ++ [i]).length = (n+2).choose 2 := by
  have hl := length_descend (LongestElementary.longest (n+2)) i (longest_descent n i)
  obtain ⟨w, hw, hwl⟩ := exists_reduced (LongestElementary.longest (n+2) * simple i)
  have hp : permutation (w ++ [i]) = LongestElementary.longest (n+2) := by
    simp only [permutation_append, permutation_singleton, hw, mul_assoc, simple,
      Equiv.swap_mul_self, mul_one]
  have hlen : (w ++ [i]).length = (n+2).choose 2 := by
    rw [List.length_append, List.length_singleton, hwl, hl, length_longest]
  refine ⟨w, ?_, hlen⟩
  unfold Reduced
  rw [hp, length_longest, hlen]

/-- EKL (2.36)–(2.37): for every `i`, the longest divided difference factors with `∂_i`
acting first, up to one global sign. -/
theorem D_factor_first (n : ℕ) (i : Fin (n+1)) :
    ∃ (L : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2)) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
      LongestDivided.D (n+2) = ε • (L ∘ₗ AllRankDivided.divided i) := by
  obtain ⟨w, hr, hl⟩ := exists_reduced_ending n i
  obtain ⟨ε, hε, h⟩ := D_eq_sign_of_reduced _ hr hl
  refine ⟨applyWord w, ε, hε, ?_⟩
  rw [h]
  congr 1
  apply LinearMap.ext
  intro f
  rw [applyWord_append]
  rfl

/-! ## Natural-index calculations -/

/-- The ordered product `x_p x_{p+1} ⋯ x_{p+k-1}`. -/
noncomputable def chain (m p : ℕ) : ℕ → SkewPolynomial (m+2)
  | 0 => 1
  | k+1 => letter m p * chain m (p+1) k

theorem cross_letter_self (m p : ℕ) (hp : p < m+1) : cross m p (letter m p) = 1 := by
  simp only [cross, letter, dif_pos hp, dif_pos (show p < m+2 by omega)]
  rw [AllRankDivided.divided_generator]
  exact if_pos (Or.inl rfl)

theorem cross_letter_succ (m p : ℕ) (hp : p < m+1) : cross m p (letter m (p+1)) = 1 := by
  simp only [cross, letter, dif_pos hp, dif_pos (show p+1 < m+2 by omega)]
  rw [AllRankDivided.divided_generator]
  exact if_pos (Or.inr rfl)

theorem cross_pair (m j : ℕ) (hj : j < m+1) :
    cross m j (letter m j * letter m (j+1)) = 0 := by
  have h := divided_balanced (⟨j, hj⟩ : Fin (m+1)) 1
  simp only [pow_one] at h
  simp only [cross, letter, dif_pos hj, dif_pos (show j < m+2 by omega),
    dif_pos (show j+1 < m+2 by omega)]
  exact h

theorem cross_chain_tail (m j q k : ℕ) (hj : j < m+1) (hq : j+1 < q) (hb : q+k ≤ m+2) :
    cross m j (chain m q k) = 0 := by
  induction k generalizing q with
  | zero => exact cross_one m j
  | succ k ih =>
      rw [chain, cross_letter_spectator m j q hj (by omega) (by omega) (by omega),
        ih (q+1) (by omega) (by omega), mul_zero]

/-- A consecutive product containing both `x_j` and `x_{j+1}` is killed by `∂_j`. -/
theorem cross_chain_inside (m j p k : ℕ) (hj : j < m+1) (hpj : p ≤ j) (hjk : j+1 < p+k)
    (hb : p+k ≤ m+2) : cross m j (chain m p k) = 0 := by
  induction k generalizing p with
  | zero => omega
  | succ k ih =>
      rw [chain]
      by_cases hjp : p = j
      · subst hjp
        obtain ⟨k, rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩
        rw [chain, ← mul_assoc, cross_mul m p hj, cross_pair m p hj, zero_mul,
          cross_chain_tail m p (p+1+1) k hj (by omega) (by omega), mul_zero, add_zero]
      · rw [cross_letter_spectator m j p hj (by omega) (by omega) (by omega),
          ih (p+1) (by omega) (by omega) (by omega), mul_zero]

theorem actNat_letter_spectator (m p : ℕ) (hp : p < m+2) (w : List ℕ)
    (hw : ∀ j ∈ w, j < m+1 ∧ p ≠ j ∧ p ≠ j+1) (f : SkewPolynomial (m+2)) :
    actNat m w (letter m p * f) = (-1 : ℤ)^w.length • (letter m p * actNat m w f) := by
  induction w with
  | nil => simp [actNat]
  | cons j w ih =>
      obtain ⟨hj, hl, hr⟩ := hw j (by simp)
      change cross m j (actNat m w (letter m p * f)) =
        (-1 : ℤ)^(j::w).length • (letter m p * cross m j (actNat m w f))
      rw [ih (fun i hi => hw i (by simp [hi])), map_smul,
        cross_letter_spectator m j p hj hp hl hr, List.length_cons, pow_succ, mul_smul,
        neg_one_smul, neg_mul, smul_neg]

theorem actNat_mul_kernel (m : ℕ) (w : List ℕ) (g : SkewPolynomial (m+2))
    (hw : ∀ j ∈ w, j < m+1 ∧ cross m j g = 0) (f : SkewPolynomial (m+2)) :
    actNat m w (f * g) = actNat m w f * g := by
  induction w with
  | nil => rfl
  | cons j w ih =>
      obtain ⟨hj, hg⟩ := hw j (by simp)
      change cross m j (actNat m w (f*g)) = cross m j (actNat m w f) * g
      rw [ih (fun i hi => hw i (by simp [hi])), cross_mul m j hj, hg, mul_zero, add_zero]

/-- The written increasing sweep `∂_p ∂_{p+1} ⋯ ∂_{p+k-1}` on `x_p ⋯ x_{p+k-1}`. -/
theorem actNat_range_chain (m p k : ℕ) (hb : p+k ≤ m+1) :
    ∃ e : ℕ, actNat m (List.range' p k) (chain m p k) = (-1 : ℤ)^e • 1 := by
  induction k generalizing p with
  | zero => exact ⟨0, by simp [actNat, chain]⟩
  | succ k ih =>
      obtain ⟨e, he⟩ := ih (p+1) (by omega)
      refine ⟨k + e, ?_⟩
      rw [List.range'_succ, chain]
      change cross m p (actNat m (List.range' (p+1) k) (letter m p * chain m (p+1) k)) = _
      rw [actNat_letter_spectator m p (by omega) _ ?_, he, List.length_range', mul_smul_comm,
        mul_one, smul_smul, map_smul, cross_letter_self m p (by omega), ← pow_add]
      intro j hj
      rw [List.mem_range'_1] at hj
      exact ⟨by omega, by omega, by omega⟩

/-- The written decreasing sweep `∂_{p+k-1} ⋯ ∂_{p+1} ∂_p` on `x_{p+1} ⋯ x_{p+k}`. -/
theorem sweep_chain (m p k : ℕ) (hb : p+k ≤ m+1) :
    ∃ e : ℕ, sweep m p k (chain m (p+1) k) = (-1 : ℤ)^e • 1 := by
  induction k generalizing p with
  | zero => exact ⟨0, by simp [sweep, chain]⟩
  | succ k ih =>
      obtain ⟨e, he⟩ := ih (p+1) (by omega)
      refine ⟨e, ?_⟩
      change sweep m (p+1) k (cross m p (chain m (p+1) (k+1))) = _
      rw [chain, cross_mul m p (by omega), cross_letter_succ m p (by omega), one_mul,
        cross_chain_tail m p (p+1+1) k (by omega) (by omega) (by omega), mul_zero,
        add_zero, he]

theorem map_range_add (p k : ℕ) : (List.range k).map (· + p) = List.range' p k := by
  rw [List.range'_eq_map_range]
  apply List.map_congr_left
  intro j _
  omega

/-- The shifted analogue of `LongestDivided.actNat_stairs`. -/
theorem actNat_stairs_shift (m p k : ℕ) (hb : p+k ≤ m+2) :
    actNat m ((coxeterWord k).map (· + p)) (stairs m p k) = (-1 : ℤ)^(k.choose 3) • 1 := by
  induction k with
  | zero => simp [coxeterWord, actNat, stairs]
  | succ k ih =>
      rw [coxeterWord, List.map_append, actNat_append, List.map_reverse, map_range_add,
        actNat_reverse_range, sweep_stairs m p k (by omega), map_smul,
        ih (by omega), smul_smul, sweepSign_choose, ← pow_add]
      rw [Nat.choose_succ_succ]

theorem sign_smul_one_ne {N : ℕ} (e : ℕ) : (-1 : ℤ)^e • (1 : SkewPolynomial N) ≠ 0 := by
  rcases neg_one_pow_eq_or ℤ e with h | h <;> simp [h]

/-! ## Peel words in rank `n+3` -/

/-- The written word `[0, 1, …, n+1]`: `∂_{n+1}` acts first and `∂_0` last. -/
def rightPeelWord (n : ℕ) : List (Fin (n+2)) := List.finRange (n+2)

/-- The written word `[n+1, …, 1, 0]`: `∂_0` acts first and `∂_{n+1}` last. -/
def leftPeelWord (n : ℕ) : List (Fin (n+2)) := (List.finRange (n+2)).reverse

/-- The rank-`(n+2)` source word on the last `n+2` of the `n+3` variables. -/
def shiftedWord (n : ℕ) : List (Fin (n+2)) := (wordIn n (n+2) le_rfl).map Fin.succ

theorem rightPeelWord_values (n : ℕ) :
    (rightPeelWord n).map Fin.val = List.range (n+2) := by
  simp [rightPeelWord]

theorem leftPeelWord_values (n : ℕ) :
    (leftPeelWord n).map Fin.val = (List.range (n+2)).reverse := by
  simp [leftPeelWord, List.map_reverse]

theorem shiftedWord_values (n : ℕ) :
    (shiftedWord n).map Fin.val = (coxeterWord (n+2)).map (· + 1) := by
  rw [shiftedWord, List.map_map, ← wordIn_values n (n+2) le_rfl, List.map_map]
  rfl

theorem wordIn_length (n k : ℕ) (h : k ≤ n+2) : (wordIn n k h).length = k.choose 2 := by
  simp [wordIn, coxeterWord_length]

theorem choose_peel (n : ℕ) : (n+2) + (n+2).choose 2 = (n+3).choose 2 := by
  have h : (n+3).choose 2 = (n+2).choose 1 + (n+2).choose 2 := Nat.choose_succ_succ (n+2) 1
  rw [h, Nat.choose_one_right]

theorem rightPeel_length (n : ℕ) :
    (rightPeelWord n ++ wordIn (n+1) (n+2) (by omega)).length = (n+3).choose 2 := by
  rw [List.length_append, wordIn_length, rightPeelWord, List.length_finRange, choose_peel]

theorem leftPeel_length (n : ℕ) :
    (leftPeelWord n ++ shiftedWord n).length = (n+3).choose 2 := by
  rw [List.length_append, shiftedWord, List.length_map, wordIn_length, leftPeelWord,
    List.length_reverse, List.length_finRange, choose_peel]

/-- The right-peel word acts by `±1` on the first-variables staircase times `x_0 ⋯ x_{n+1}`. -/
theorem rightPeel_apply (n : ℕ) :
    ∃ e : ℕ, applyWord (rightPeelWord n ++ wordIn (n+1) (n+2) (by omega))
      (stairs (n+1) 0 (n+2) * chain (n+1) 0 (n+2)) = (-1 : ℤ)^e • 1 := by
  obtain ⟨e, he⟩ := actNat_range_chain (n+1) 0 (n+2) (by omega)
  refine ⟨(n+2).choose 3 + e, ?_⟩
  rw [applyWord_append, ← actNat_map_fin, ← actNat_map_fin, wordIn_values,
    rightPeelWord_values, actNat_mul_kernel, actNat_stairs (n+1) (n+2) (by omega),
    smul_mul_assoc, one_mul, map_smul, List.range_eq_range', he, smul_smul, ← pow_add]
  intro j hj
  have := coxeterWord_bound hj
  exact ⟨by omega, cross_chain_inside (n+1) j 0 (n+2) (by omega) (by omega) (by omega)
    (by omega)⟩

/-- The left-peel word acts by `±1` on the last-variables staircase times `x_1 ⋯ x_{n+2}`. -/
theorem leftPeel_apply (n : ℕ) :
    ∃ e : ℕ, applyWord (leftPeelWord n ++ shiftedWord n)
      (stairs (n+1) 1 (n+2) * chain (n+1) 1 (n+2)) = (-1 : ℤ)^e • 1 := by
  obtain ⟨e, he⟩ := sweep_chain (n+1) 0 (n+2) (by omega)
  refine ⟨(n+2).choose 3 + e, ?_⟩
  rw [applyWord_append, ← actNat_map_fin, ← actNat_map_fin, shiftedWord_values,
    leftPeelWord_values, actNat_mul_kernel, actNat_stairs_shift (n+1) 1 (n+2) (by omega),
    smul_mul_assoc, one_mul, map_smul, List.range_eq_range', actNat_reverse_range, he,
    smul_smul, ← pow_add]
  intro j hj
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
  have := coxeterWord_bound hi
  exact ⟨by omega, cross_chain_inside (n+1) (i+1) 1 (n+2) (by omega) (by omega) (by omega)
    (by omega)⟩

theorem rightPeel_reduced (n : ℕ) :
    Reduced (rightPeelWord n ++ wordIn (n+1) (n+2) (by omega)) := by
  obtain ⟨e, he⟩ := rightPeel_apply n
  exact reduced_of_apply_ne _ _ (he ▸ sign_smul_one_ne e)

theorem rightPeel_permutation (n : ℕ) :
    permutation (rightPeelWord n ++ wordIn (n+1) (n+2) (by omega)) =
      LongestElementary.longest (n+3) :=
  eq_longest_of_length _ ((rightPeel_reduced n).symm.trans (rightPeel_length n))

theorem leftPeel_reduced (n : ℕ) : Reduced (leftPeelWord n ++ shiftedWord n) := by
  obtain ⟨e, he⟩ := leftPeel_apply n
  exact reduced_of_apply_ne _ _ (he ▸ sign_smul_one_ne e)

theorem leftPeel_permutation (n : ℕ) :
    permutation (leftPeelWord n ++ shiftedWord n) = LongestElementary.longest (n+3) :=
  eq_longest_of_length _ ((leftPeel_reduced n).symm.trans (leftPeel_length n))

/-- Right-peel factorization: `D (n+3) = ± (∂_0 ∂_1 ⋯ ∂_{n+1}) ∘ D_{n+2}` with the
rank-`(n+2)` source word acting first on the first `n+2` variables. -/
theorem D_factor_right_peel (n : ℕ) : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    LongestDivided.D (n+3) = ε • (LongestDivided.applyWord (rightPeelWord n) ∘ₗ
      LongestDivided.applyWord (LongestDivided.wordIn (n+1) (n+2) (by omega))) := by
  obtain ⟨ε, hε, h⟩ := D_eq_sign_of_reduced _ (rightPeel_reduced n) (rightPeel_length n)
  refine ⟨ε, hε, ?_⟩
  rw [h]
  congr 1
  apply LinearMap.ext
  intro f
  rw [applyWord_append]
  rfl

/-- Left-peel factorization: `D (n+3) = ± (∂_{n+1} ⋯ ∂_1 ∂_0) ∘ D'_{n+2}` with the
rank-`(n+2)` source word acting first on the last `n+2` variables. -/
theorem D_factor_left_peel (n : ℕ) : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    LongestDivided.D (n+3) = ε • (LongestDivided.applyWord (leftPeelWord n) ∘ₗ
      LongestDivided.applyWord (shiftedWord n)) := by
  obtain ⟨ε, hε, h⟩ := D_eq_sign_of_reduced _ (leftPeel_reduced n) (leftPeel_length n)
  refine ⟨ε, hε, ?_⟩
  rw [h]
  congr 1
  apply LinearMap.ext
  intro f
  rw [applyWord_append]
  rfl

/-! ## Degree bounds -/

/-- The degree-zero piece consists of constants. -/
theorem piece_zero_eq {N : ℕ} {f : SkewPolynomial N} (hf : f ∈ polynomialPiece N 0) :
    f = f 0 • 1 := by
  have h1 : (1 : SkewPolynomial N) = monomial 0 1 := rfl
  ext a
  rw [h1, Finsupp.smul_apply, smul_eq_mul]
  by_cases ha : a = 0
  · subst ha
    simp
  · rw [Finsupp.single_eq_of_ne (Ne.symm ha), mul_zero]
    apply hf a
    intro hd
    apply ha
    funext j
    have hs : (∑ i, a i) = 0 := by dsimp [pdegree] at hd; omega
    exact (Finset.sum_eq_zero_iff.mp hs) j (Finset.mem_univ j)

/-- Every word lowers the degree of a monomial by its length. -/
theorem applyWord_monomial_mem {n : ℕ} (w : Word n) (γ : Fin (n+2) → ℕ) (c : ℤ) :
    applyWord w (monomial γ c) ∈
      polynomialPiece (n+2) (2*((∑ j, γ j : ℕ) : ℤ) - 2*(w.length : ℤ)) :=
  applyWord_mem w (monomial_mem γ c)

theorem applyWord_monomial_low {n : ℕ} (w : Word n) (γ : Fin (n+2) → ℕ) (c : ℤ)
    (h : ∑ j, γ j < w.length) : applyWord w (monomial γ c) = 0 := by
  have hm := applyWord_monomial_mem w γ c
  rw [polynomial_negative _ _ (by omega)] at hm
  exact hm

theorem applyWord_monomial_top {n : ℕ} (w : Word n) (γ : Fin (n+2) → ℕ) (c : ℤ)
    (h : ∑ j, γ j = w.length) :
    applyWord w (monomial γ c) = (applyWord w (monomial γ c) 0) • 1 := by
  have hm := applyWord_monomial_mem w γ c
  rw [show 2*((∑ j, γ j : ℕ) : ℤ) - 2*(w.length : ℤ) = 0 by omega] at hm
  exact piece_zero_eq hm

/-- `D N` lowers degree by `C(N,2)` in every rank, including the identity ranks `0, 1`. -/
theorem D_mem (N : ℕ) {d : ℤ} {f : SkewPolynomial N} (hf : f ∈ polynomialPiece N d) :
    LongestDivided.D N f ∈ polynomialPiece N (d - 2*(N.choose 2 : ℤ)) := by
  rcases N with _ | _ | n
  · simpa using hf
  · simpa using hf
  · rw [D_eq_inherited, ← sourceWord_length n]
    exact applyWord_mem _ hf

theorem D_monomial_low_degree (N : ℕ) (γ : Fin N → ℕ) (c : ℤ) (h : ∑ j, γ j < N.choose 2) :
    LongestDivided.D N (monomial γ c) = 0 := by
  have hm := D_mem N (monomial_mem γ c)
  rw [polynomial_negative _ _ (by dsimp [pdegree]; omega)] at hm
  exact hm

theorem D_monomial_top_degree (N : ℕ) (γ : Fin N → ℕ) (c : ℤ) (h : ∑ j, γ j = N.choose 2) :
    LongestDivided.D N (monomial γ c) = (LongestDivided.D N (monomial γ c) 0) • 1 := by
  have hm := D_mem N (monomial_mem γ c)
  rw [show pdegree γ - 2*(N.choose 2 : ℤ) = 0 by dsimp [pdegree]; omega] at hm
  exact piece_zero_eq hm

end OddMath.Frontier.LongestFactor
