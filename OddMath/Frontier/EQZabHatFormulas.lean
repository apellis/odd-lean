import OddMath.Frontier.EQZabDual

/-!
# The hat versions of the SZ relation, the Pieri rule and Proposition 3.11

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3.2, the three displayed formulas (4.18)–(4.20) after Lemma 4.5 (printed numbering), stated
there without proof:

1. (4.18) `s̃̂_λ 1_z = 1_z w₀(ŝ_λ)` (hat SZ relation, in `Z_n` with `1_z f = (θ ∘ w₀)(f) 1_z`);
2. (4.19) `ẽ_1 s̃̂_λ = Σ_{μ = λ + □_i} (-1)^{binom(n-1,2) + |λ/i|} s̃̂_μ` (hat Pieri rule);
3. (4.20) `d(ŝ_λ) = (-1)^{binom(n-1,2)} Σ_{μ = λ + □_i} (-1)^{|i/λ| + i - 1} {ct(□_i)} ŝ_μ`.

Rows are numbered from `0` here; `rowsAbove λ i = |λ/i|`, `rowsBelow λ i = |i/λ|`.

* (1) holds as printed (`hat_sz`).
* (2) is **false as printed** (`hat_pieri_printed_false`, already for `n = 2`, `λ = ∅`); the
  correct sign is `(-1)^{binom(n,2) + |i/λ|}` (`hat_pieri`, for every exponent vector;
  `hat_pieri_partition` for partitions, summing over `μ = λ + □_i`).
* (3) is **false as printed** (`hat_d_printed_false`, `n = 2`, `λ = (1)`); the correct formula
  is `d(ŝ_λ) = Σ_i (-1)^{binom(n,2) + |i/λ|} {ct(□_i)} ŝ_{λ + □_i}` (`hat_d`, every exponent
  vector, `ct(□_i) = λ_i - i`; `hat_d_partition` for partitions, summing over `μ = λ + □_i`).

Both corrections come from the correction factor of Lemma 4.5 (`EQZabHat.twistedHat_eq_D`,
`lemma_4_5_top`): `hatCorr` changes by `(-1)^{n-1-i}` when a box is added in row `i`.
-/

namespace OddMath.Frontier.EQZab

open OddMath.SkewPolynomial (SkewPolynomial generator monomial expSingle)
open EQSkewDifferential EQSchur
open scoped BigOperators

noncomputable section

local instance (priority := high) zabHFNUNASemiring (m : ℕ) :
    NonUnitalNonAssocSemiring (SkewPolynomial m) :=
  @NonAssocSemiring.toNonUnitalNonAssocSemiring _
    (@Semiring.toNonAssocSemiring _ (OddMath.PbwL3.instSemiring m))

local instance (priority := high) zabHFNUNARing (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

variable {N : ℕ}

/-! ## (1) The hat SZ relation -/

/-- **Hat SZ relation** (as printed): `s̃̂_λ = (θ ∘ w₀)(w₀(ŝ_λ))`, i.e. `s̃̂_λ 1_z = 1_z w₀(ŝ_λ)` in
`Z_n`. -/
theorem hat_sz (l : Fin N → ℕ) :
    twistedHat N l = twistRev N (longestPerm N (untwistedHat N l)) := by
  rw [twistRev, RingHom.comp_apply, longestPerm_longestPerm, untwistedHat_eq_theta, theta_theta]

/-! ## Sign bookkeeping -/

theorem stairDot_add_expSingle (l : Fin N → ℕ) (i : Fin N) :
    stairDot (l + expSingle i) = stairDot l + (N - 1 - i.val) := by
  simp [stairDot, add_mul, Finset.sum_add_distrib, expSingle]

theorem pairSum_expSingle (i : Fin N) : pairSum (expSingle i : Fin N → ℕ) = 0 := by
  unfold pairSum
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  split_ifs with h
  · simp only [expSingle]
    split_ifs with h1 h2 <;> first | simp | (subst h1; subst h2; exact absurd h (lt_irrefl _))
  · rfl

theorem pairSum_add_expSingle (l : Fin N → ℕ) (i : Fin N) :
    pairSum (l + expSingle i) + l i = pairSum l + ∑ j, l j := by
  have h1 := pairSum_add l (expSingle i)
  have h2 := crossingCount_add_swap l (expSingle i)
  have h3 : ∑ j, l j * (expSingle i : Fin N → ℕ) j = l i := by
    simp [expSingle, mul_ite]
  have h4 : ∑ j, (expSingle i : Fin N → ℕ) j = 1 := by simp [expSingle]
  rw [pairSum_expSingle, add_zero] at h1
  rw [h3, h4, mul_one] at h2
  omega

theorem crossingCount_expSingle_left (l : Fin N → ℕ) (i : Fin N) :
    OddMath.crossingCount (expSingle i) l = rowsAbove l i := by
  unfold OddMath.crossingCount
  rw [rowsAbove_eq]
  simp only [expSingle, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp [Finset.sum_filter]
  · intro k _ hk
    exact Finset.sum_eq_zero fun j _ => ite_eq_right (fun h => absurd h.symm hk)
  · simp

/-- `ε_1 ∂_{w₀}(g) = (-1)^{binom(N-1,2)} ∂_{w₀}(ε_1 g)`. -/
theorem elementaryPoly_one_mul_D (g : SkewPolynomial N) :
    FiniteCompleteElementary.elementaryPoly N 1 * LongestDivided.D N g =
      (-1 : ℤ) ^ (N-1).choose 2 •
        LongestDivided.D N (FiniteCompleteElementary.elementaryPoly N 1 * g) := by
  rcases N with _ | _ | n
  · simp [LongestDivided.D]
  · simp [LongestDivided.D]
  · show FiniteCompleteElementary.elementaryPoly (n+2) 1 * LongestDivided.D (n+2) g =
      (-1 : ℤ) ^ (n+2-1).choose 2 •
        LongestDivided.D (n+2) (FiniteCompleteElementary.elementaryPoly (n+2) 1 * g)
    have hk : FiniteCompleteElementary.elementaryPoly (n+2) 1 ∈
        OddSymmetricKernel.kernelSubring n :=
      OddSymmetricKernel.elementary_mem n 1
    have hw := LongestElementary.action_elementary (n+2) 1
    have h := OddSymmetrizer.D_left_kernel n _ g hk
    rw [hw] at h
    simp only [one_mul, show n + 2 - 1 = n + 1 by omega] at h
    rw [h, smul_mul_assoc, smul_smul, show n + 2 - 1 = n + 1 by omega,
      show Nat.choose 1 2 = 0 from rfl, zero_add, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
      one_pow, one_smul]

theorem elementaryPoly_one_eq (N : ℕ) :
    FiniteCompleteElementary.elementaryPoly N 1 = ∑ i : Fin N, (-1 : ℤ) ^ i.val • generator i := by
  rw [FiniteCompleteElementary.elementaryPoly_eq_strictSum, strictSum_one]
  rfl

/-! ## (2) The hat Pieri rule -/

/-- **Hat Pieri rule, corrected**: for every exponent vector `λ`,
`ẽ_1 s̃̂_λ = Σ_i (-1)^{binom(n,2) + |i/λ|} s̃̂_{λ + ε_i}`. -/
theorem hat_pieri (l : Fin N → ℕ) :
    FiniteCompleteElementary.elementaryPoly N 1 * twistedHat N l =
      ∑ i, (-1 : ℤ) ^ (N.choose 2 + rowsBelow l i) • twistedHat N (l + expSingle i) := by
  rw [twistedHat_eq_D, mul_smul_comm, elementaryPoly_one_mul_D, elementaryPoly_one_eq,
    Finset.sum_mul, map_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, map_zsmul, show generator i = monomial (expSingle i) 1 from rfl,
    show monomial (expSingle i) 1 * (monomial l 1 * LongestDivided.staircase N) =
      monomial (expSingle i) 1 * monomial l 1 * LongestDivided.staircase N from
      (OddMath.SkewPolynomial.mul_assoc _ _ _).symm, OddSchurPieri.mono_mul, smul_mul_assoc, map_zsmul,
    OddMath.skewSign, crossingCount_expSingle_left, add_comm (expSingle i) l, twistedHat_eq_D,
    smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  have hsd := stairDot_add_expSingle l i
  have hps := pairSum_add_expSingle l i
  have hsum := sum_eq_rowsAbove_add l i
  have hi := i.isLt
  have hc : N.choose 2 = (N-1).choose 2 + (N-1) := by
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    rw [choose_two_succ, show m + 1 - 1 = m by omega]
  simp only [hatCorr, ← pow_add]
  apply MonomialReversal.neg_one_pow_of_even_add
  refine ⟨(N+1).choose 4 + stairDot l + pairSum l + (N-1).choose 2 + rowsAbove l i +
    rowsBelow l i + (N - 1), ?_⟩
  omega

open Classical in
/-- **Hat Pieri rule, corrected**, for a partition `λ`: the sum runs over the partitions
`μ = λ + □_i`. -/
theorem hat_pieri_partition (l : Fin N → ℕ) (hl : Antitone l) :
    FiniteCompleteElementary.elementaryPoly N 1 * twistedHat N l =
      ∑ i, if Antitone (l + expSingle i) then
        (-1 : ℤ) ^ (N.choose 2 + rowsBelow l i) • twistedHat N (l + expSingle i) else 0 := by
  rw [hat_pieri]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · rw [lemma_4_5_bottom, twisted_eq_theta_untwisted, untwisted_add_expSingle_eq_zero hl h,
      map_zero, map_zero, smul_zero, smul_zero]

/-! ## (3) The differential of `ŝ_λ` -/

theorem d_longestPerm_N (f : SkewPolynomial N) :
    d N (longestPerm N f) = longestPerm N (d N f) := by
  let D : SkewPolynomial N →+ SkewPolynomial N := (d N).comp (longestPerm N).toAddMonoidHom
  let E : SkewPolynomial N →+ SkewPolynomial N := (longestPerm N).toAddMonoidHom.comp (d N)
  exact deriv_ext (D := D) (E := E) ((parityInv N).comp (longestPerm N)) (longestPerm N)
    (fun f g => by simp [D, d_mul])
    (fun f g => by simp [E, d_mul, EQSchur.parityInv_longestPerm])
    (fun j => by simp [D, E]) f

/-- **The differential of `ŝ_λ`, corrected**: for every exponent vector `λ`,
`d(ŝ_λ) = Σ_i (-1)^{binom(n,2) + |i/λ|} {λ_i - i} ŝ_{λ + ε_i}` (rows from `0`). -/
theorem hat_d (l : Fin N → ℕ) :
    d N (untwistedHat N l) =
      ∑ i, ((-1 : ℤ) ^ (N.choose 2 + rowsBelow l i) * (content l i % 2)) •
        untwistedHat N (l + expSingle i) := by
  rw [lemma_4_5_top, map_zsmul, d_longestPerm_N, d_untwisted, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, smul_smul, lemma_4_5_top, smul_smul]
  congr 1
  have hsd := stairDot_add_expSingle l i
  have hps := pairSum_add_expSingle l i
  have hsum := sum_eq_rowsAbove_add l i
  have hsum' : ∑ j, (l + expSingle i) j = ∑ j, l j + 1 := by
    simp [Finset.sum_add_distrib, expSingle]
  have hi := i.isLt
  have hc : N.choose 2 = (N-1).choose 2 + (N-1) := by
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    rw [choose_two_succ, show m + 1 - 1 = m by omega]
  rw [hsum']
  simp only [hatCorr]
  have key : (-1 : ℤ) ^ ((N+1).choose 4 + stairDot l) *
        (-1) ^ (N.choose 3 + (N-1).choose 2 * ∑ j, l j + pairSum l) *
        (-1) ^ (rowsAbove l i + i.val) *
        ((-1) ^ ((N+1).choose 4 + stairDot (l + expSingle i)) *
          (-1) ^ (N.choose 3 + (N-1).choose 2 * (∑ j, l j + 1) + pairSum (l + expSingle i))) =
      (-1) ^ (N.choose 2 + rowsBelow l i) := by
    simp only [← pow_add]
    apply MonomialReversal.neg_one_pow_of_even_add
    rw [hsd, mul_add, mul_one]
    generalize (N-1).choose 2 * ∑ j, l j = P at *
    refine ⟨(N+1).choose 4 + stairDot l + N.choose 3 + P + pairSum l + rowsAbove l i +
      rowsBelow l i + (N-1).choose 2 + (N - 1), ?_⟩
    omega
  have hsq := ((IsSign.pow ((N+1).choose 4 + stairDot (l + expSingle i))).mul
    (IsSign.pow (N.choose 3 + (N-1).choose 2 * (∑ j, l j + 1) +
      pairSum (l + expSingle i)))).mul_self
  linear_combination (content l i % 2 * ((-1 : ℤ) ^ ((N+1).choose 4 + stairDot (l + expSingle i)) *
      (-1) ^ (N.choose 3 + (N-1).choose 2 * (∑ j, l j + 1) + pairSum (l + expSingle i)))) * key -
    ((-1 : ℤ) ^ ((N+1).choose 4 + stairDot l) *
      (-1) ^ (N.choose 3 + (N-1).choose 2 * ∑ j, l j + pairSum l) *
      (-1) ^ (rowsAbove l i + i.val) * (content l i % 2)) * hsq

open Classical in
/-- **The differential of `ŝ_λ`, corrected**, for a partition `λ`: the sum runs over the partitions
`μ = λ + □_i`. -/
theorem hat_d_partition (l : Fin N → ℕ) (hl : Antitone l) :
    d N (untwistedHat N l) =
      ∑ i, if Antitone (l + expSingle i) then
        ((-1 : ℤ) ^ (N.choose 2 + rowsBelow l i) * (content l i % 2)) •
          untwistedHat N (l + expSingle i) else 0 := by
  rw [hat_d]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · rw [lemma_4_5_top, untwisted_add_expSingle_eq_zero hl h, map_zero, smul_zero, smul_zero]

/-! ## Refutations of the printed forms -/

/-- Evaluation `x_0 ↦ 1`, `x_1 ↦ 0` on `OPol_2` (a ring map to `ℤ`). -/
def ev2 : SkewPolynomial 2 →+* ℤ :=
  skewLift ![1, 0] (fun i j h => by fin_cases i <;> fin_cases j <;> simp_all)

theorem ev2_generator_zero : ev2 (generator 0) = 1 := by simp [ev2]
theorem ev2_generator_one : ev2 (generator 1) = 0 := by simp [ev2]

theorem elementaryPoly_two_one :
    FiniteCompleteElementary.elementaryPoly 2 1 = generator 0 - generator 1 := by
  rw [elementaryPoly_one_eq, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

theorem twistedHat_two_zero : twistedHat 2 0 = 1 := by
  rw [twistedHat_eq_D, show monomial (0 : Fin 2 → ℕ) 1 = (1 : SkewPolynomial 2) from rfl, one_mul,
    LongestDivided.D_staircase]
  simp [hatCorr, stairDot, pairSum, Nat.choose]

/-- The hat Pieri rule is false as printed (`n = 2`, `λ = ∅`). -/
theorem hat_pieri_printed_false :
    ¬ ∀ (N : ℕ) (l : Fin N → ℕ), Antitone l →
      FiniteCompleteElementary.elementaryPoly N 1 * twistedHat N l =
        ∑ i, if Antitone (l + expSingle i) then
          (-1 : ℤ) ^ ((N-1).choose 2 + rowsAbove l i) • twistedHat N (l + expSingle i)
        else 0 := by
  intro h
  have h1 := h 2 0 (fun _ _ _ => le_rfl)
  have h2 := hat_pieri_partition (0 : Fin 2 → ℕ) (fun _ _ _ => le_rfl)
  rw [h1] at h2
  have h3 := congrArg ev2 h2
  simp only [Fin.sum_univ_two, map_add] at h3
  have hA0 : Antitone ((0 : Fin 2 → ℕ) + expSingle 0) := by
    intro p q hpq; fin_cases p <;> fin_cases q <;> simp_all [expSingle]
  have hA1 : ¬ Antitone ((0 : Fin 2 → ℕ) + expSingle 1) := by
    intro hA; have := hA (show (0 : Fin 2) ≤ 1 by decide); simp [expSingle] at this
  simp only [hA0, hA1, ite_true, ite_false, map_zero, add_zero, map_zsmul] at h3
  have hr : rowsAbove (0 : Fin 2 → ℕ) 0 = 0 := by simp [rowsAbove]
  have hb : rowsBelow (0 : Fin 2 → ℕ) 0 = 0 := by simp [rowsBelow]
  rw [hr, hb] at h3
  have hv : ev2 (FiniteCompleteElementary.elementaryPoly 2 1 * twistedHat 2 0) = 1 := by
    rw [twistedHat_two_zero, mul_one, elementaryPoly_two_one, map_sub, ev2_generator_zero,
      ev2_generator_one, sub_zero]
  have h4 := hat_pieri_partition (0 : Fin 2 → ℕ) (fun _ _ _ => le_rfl)
  have h5 := congrArg ev2 h4
  simp only [Fin.sum_univ_two, hA0, hA1, ite_true, ite_false, add_zero, map_zsmul, hb] at h5
  rw [hv] at h5
  norm_num at h3 h5
  omega

theorem untwisted_two_zero_ne_zero : untwisted 2 ![2, 0] ≠ 0 := by
  intro h0
  have hm : monomial (![2, 0] : Fin 2 → ℕ) 1 = generator 0 * generator 0 := by
    rw [MonomialReversal.monomial_eq_prod]
    simp [pow_two]
  have hs : LongestDivided.staircase 2 = generator 0 := by
    rw [staircase_eq_monomial]
    show monomial _ 1 = monomial (expSingle 0) 1
    congr 1; funext j; fin_cases j <;> rfl
  have hin : theta 2 (LongestDivided.staircase 2) * theta 2 (monomial ![2, 0] 1) =
      generator (0 : Fin 1).castSucc * (generator (0 : Fin 1).castSucc *
        generator (0 : Fin 1).castSucc) := by
    rw [hs, hm, map_mul, theta_generator]
    simp
  have hD : ∀ f, LongestDivided.D 2 f = AllRankDivided.divided (0 : Fin 1) f := fun f => rfl
  rw [untwisted, hin, hD, AllRankDivided.divided_left_mul, AllRankDivided.divided_left_mul,
    AllRankDivided.divided_generator] at h0
  have h1 := congrArg (fun f => ev2 (longestPerm 2 (theta 2 f))) h0
  have g0 : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := rfl
  have g1 : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := rfl
  simp [ev2, g0, g1] at h1

/-- The printed formula for `d(ŝ_λ)` is false (`n = 2`, `λ = (1)`). -/
theorem hat_d_printed_false :
    ¬ ∀ (N : ℕ) (l : Fin N → ℕ), Antitone l →
      d N (untwistedHat N l) =
        ∑ i, if Antitone (l + expSingle i) then
          ((-1 : ℤ) ^ ((N-1).choose 2 + rowsBelow l i + i.val) * (content l i % 2)) •
            untwistedHat N (l + expSingle i)
        else 0 := by
  intro h
  have hl : Antitone (![1, 0] : Fin 2 → ℕ) := by
    intro p q hpq; fin_cases p <;> fin_cases q <;> simp_all
  have h1 := h 2 ![1, 0] hl
  rw [hat_d, Fin.sum_univ_two, Fin.sum_univ_two] at h1
  have e0 : (![1, 0] : Fin 2 → ℕ) + expSingle 0 = ![2, 0] := by
    funext j; fin_cases j <;> rfl
  have e1 : (![1, 0] : Fin 2 → ℕ) + expSingle 1 = ![1, 1] := by
    funext j; fin_cases j <;> rfl
  have a0 : Antitone (![2, 0] : Fin 2 → ℕ) := by
    intro p q hpq; fin_cases p <;> fin_cases q <;> simp_all
  have a1 : Antitone (![1, 1] : Fin 2 → ℕ) := by
    intro p q hpq; fin_cases p <;> fin_cases q <;> simp_all
  rw [e0, e1, ite_eq_left a0, ite_eq_left a1] at h1
  have c0 : ((-1 : ℤ) ^ (Nat.choose 2 2 + rowsBelow ![1, 0] (0 : Fin 2)) *
      (content ![1, 0] 0 % 2)) = -1 := by decide
  have c1 : ((-1 : ℤ) ^ (Nat.choose 2 2 + rowsBelow ![1, 0] (1 : Fin 2)) *
      (content ![1, 0] 1 % 2)) = -1 := by decide
  have p0 : ((-1 : ℤ) ^ ((2-1).choose 2 + rowsBelow ![1, 0] (0 : Fin 2) + (0 : Fin 2).val) *
      (content ![1, 0] 0 % 2)) = 1 := by decide
  have p1 : ((-1 : ℤ) ^ ((2-1).choose 2 + rowsBelow ![1, 0] (1 : Fin 2) + (1 : Fin 2).val) *
      (content ![1, 0] 1 % 2)) = -1 := by decide
  rw [c0, c1, p0, p1] at h1
  have h2 : untwistedHat 2 ![2, 0] = 0 := by
    ext m
    have := congrArg (fun f : SkewPolynomial 2 => f m) h1
    simp at this
    simp
    omega
  rw [lemma_4_5_top] at h2
  have h4 := congrArg (fun f => longestPerm 2 f) (smul_eq_zero.mp h2 |>.resolve_left
    (by unfold hatCorr; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))))
  simp only [longestPerm_longestPerm, map_zero] at h4
  exact untwisted_two_zero_ne_zero h4

end

end OddMath.Frontier.EQZab
