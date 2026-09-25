import OddMath.Frontier.ThickMatrixUnits
import OddMath.Frontier.StaircaseEvaluation
import OddMath.Frontier.PrefixEmbedding
import OddMath.Frontier.EKLSectionTwoC

/-! # Miscellaneous statements of EKL §§2, 4

EKL arXiv:1111.1320v1.

* p. 34, after (4.20): `χ^a_{(1^r)} = C(a,3) + r C(a,2) + r(3a² − 3ar + r² − 1)/6`
  (`chi_col`, `chi_col_div`). True as printed, for `0 ≤ r ≤ a`.
* p. 42, (4.52): `X^{a,1}_{(1^r)} = a(a−r) + C(a−r+1,2)`, with `X^{a,b}_α` from (4.51)
  (`ThickBubble.signX`). Only true mod 2 (`signX_col_mod_two`). The exact value is
  `X^{a,1}_{(1^r)} = r(a−r) + C(a,3) + a C(a,2) + 2 C(a+1,3) − C(a−r,2)` (`signX_col_exact`);
  (4.52) fails for `a = r = 2` (`eq_4_52_false`).
* p. 42, "In particular, `X^{a,1}_{(1^a)} = 1`": false for every `a ≥ 1`, even mod 2:
  `X^{a,1}_{(1^a)}` is even (`signX_col_self_even`), so `(−1)^{X^{a,1}_{(1^a)}} = 1`.

* Prop 4.5 (4.28), p. 35, with `D_m` acting on the first `m` of `a ≥ m` variables: from the
  rank-`m` statement `StaircaseEvaluation.prop_4_5` along the prefix embedding
  (`applyWord_prefix_eq_zero`, `prop_4_5_prefix`, `prop_4_5_rank`).
* (2.44), p. 11, second line: `rk_q(ONH_a) = q^{−a(a−1)/2} [a]! / (1 − q²)^a` in `ℤ((q))`
  (`eq_2_44`, `eq_2_44_mul`), with `rk_q(ONH_a)` the Laurent series of the ranks of the degree
  pieces `NilHeckeGrading.degreePiece` (`onhRank`).

Here `(1^r) ∈ P(a,1)` is `ThickMatrixUnits.col a r`. -/

namespace OddMath.Frontier.EKLMisc
open ThickBubble ThickMatrixUnits BoxComplement
open scoped BigOperators

/-! ## p. 34: `χ^a_{(1^r)}` -/

/-- `6 Σ_{i<r} C(a−i,2) = r(3a² − 3ar + r² − 1)` for `r ≤ a`. -/
theorem six_sum_choose_two (a r : ℕ) (hr : r ≤ a) :
    6 * (∑ i ∈ Finset.range r, ((a - i).choose 2 : ℤ)) =
      r * (3 * a ^ 2 - 3 * a * r + r ^ 2 - 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    obtain ⟨m, hm⟩ : ∃ m, a - r = m + 1 := ⟨a - r - 1, by omega⟩
    have hc : ((m + 1).choose 2 : ℤ) * 2 = (m + 1) * m := by
      have := Nat.succ_mul_choose_eq m 1
      rw [Nat.choose_one_right] at this
      exact_mod_cast this.symm
    have ha : (a : ℤ) = r + m + 1 := by omega
    rw [Finset.sum_range_succ, mul_add, ih (by omega), hm]
    push_cast
    rw [ha] at *
    linear_combination 3 * hc

/-- EKL p. 34, after (4.20), over `ℤ` without division:
`6 χ^a_{(1^r)} = 6 C(a,3) + 6 r C(a,2) + r(3a² − 3ar + r² − 1)`, `a = n+2`, `r ≤ a`. -/
theorem chi_col {n r : ℕ} (hr : r ≤ n+2) :
    6 * (ThickDots.chi (col (n+2) r) : ℤ) =
      6 * (n+2).choose 3 + 6 * r * (n+2).choose 2 +
        r * (3 * (n+2 : ℤ) ^ 2 - 3 * (n+2) * r + r ^ 2 - 1) := by
  have h : ThickDots.chi (col (n+2) r) = _ := blockChi_col (ν := n+2) (k := r) (by omega) hr
  rw [h]
  push_cast
  have := six_sum_choose_two (n+2) r hr
  push_cast at this
  linear_combination this

/-- EKL p. 34, after (4.20), as printed: `χ^a_{(1^r)} = C(a,3) + r C(a,2) + r(3a² − 3ar + r² − 1)/6`
for `a = n+2` and `0 ≤ r ≤ a`; the division is exact. -/
theorem chi_col_div {n r : ℕ} (hr : r ≤ n+2) :
    (6 : ℤ) ∣ r * (3 * (n+2 : ℤ) ^ 2 - 3 * (n+2) * r + r ^ 2 - 1) ∧
    (ThickDots.chi (col (n+2) r) : ℤ) =
      (n+2).choose 3 + r * (n+2).choose 2 +
        r * (3 * (n+2 : ℤ) ^ 2 - 3 * (n+2) * r + r ^ 2 - 1) / 6 := by
  have h := chi_col hr
  have hd : (6 : ℤ) ∣ r * (3 * (n+2 : ℤ) ^ 2 - 3 * (n+2) * r + r ^ 2 - 1) :=
    ⟨ThickDots.chi (col (n+2) r) - (n+2).choose 3 - r * (n+2).choose 2, by linear_combination -h⟩
  refine ⟨hd, ?_⟩
  obtain ⟨t, ht⟩ := hd
  rw [ht, Int.mul_ediv_cancel_left t (by norm_num)]
  have h6 : (6 : ℤ) * ThickDots.chi (col (n+2) r) =
      6 * ((n+2).choose 3 + r * (n+2).choose 2 + t) := by
    linear_combination h + ht
  exact mul_left_cancel₀ (by norm_num) h6

/-! ## p. 42: `X^{a,1}_{(1^r)}` -/

/-- The exact value of (4.51) at `α = (1^r) ∈ P(a,1)`:
`X^{a,1}_{(1^r)} + C(a−r,2) = r(a−r) + C(a,3) + a C(a,2) + 2 C(a+1,3)`. -/
theorem signX_col_exact {a r : ℕ} (ha : 1 ≤ a) (hr : r ≤ a) :
    signX a 1 (col a r) + (a - r).choose 2 =
      r * (a - r) + a.choose 3 + a * a.choose 2 + 2 * (a + 1).choose 3 := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + r := ⟨a - r, by omega⟩
  simp only [signX, bubbleSign, blockChi_col ha hr, hat_col, StaircaseEvaluation.omega,
    Finset.univ_unique, Finset.sum_singleton, sum_col hr]
  simp only [blockChi, Nat.add_sub_cancel, Fin.default_eq_zero, Fin.val_zero, zero_add,
    Fin.rev_zero, Nat.choose_eq_zero_of_lt (by norm_num : 1 < 2), add_zero]
  have F1 := hockey r c
  have F1' : ∑ i ∈ Finset.range r, (c + r - i).choose 2 =
      ∑ i ∈ Finset.range r, (r + c - i).choose 2 :=
    Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm c r]
  have F2 : (c+1).choose 3 = c.choose 3 + c.choose 2 := by
    have := Nat.choose_succ_succ' c 2; simp only [Nat.reduceAdd] at this; omega
  rw [show r + c + 1 = c + r + 1 by omega] at F1
  have F4 : r * (c + r).choose 2 + (c + r).choose 2 * c = (c + r) * (c + r).choose 2 := by ring
  omega

/-- (4.52) holds mod 2: `X^{a,1}_{(1^r)} ≡ a(a−r) + C(a−r+1,2)`. -/
theorem signX_col_mod_two {a r : ℕ} (ha : 1 ≤ a) (hr : r ≤ a) :
    signX a 1 (col a r) % 2 = (a * (a - r) + (a - r + 1).choose 2) % 2 := by
  have h := signX_col ha hr
  obtain ⟨c, rfl⟩ : ∃ c, a = c + r := ⟨a - r, by omega⟩
  rw [show c + r - r = c by omega]
  have F1 := ThickMatrixUnits.choose_two_add r c
  have F2 : (c+1).choose 2 = c.choose 2 + c := by
    have := Nat.choose_succ_succ' c 1; simp only [Nat.choose_one_right, Nat.reduceAdd] at this
    omega
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self c
  have F3 : (c + r) * c = c * c + c * r := by ring
  have F4 : c * (c + 1) = c * c + c := by ring
  omega

/-- (4.52) is false as an equality of integers: for `a = r = 2`, (4.51) gives `4`, (4.52) `0`. -/
theorem eq_4_52_false :
    signX 2 1 (col 2 2) = 4 ∧ 2 * (2 - 2) + (2 - 2 + 1).choose 2 = 0 := by
  have h := signX_col_exact (a := 2) (r := 2) (by norm_num) le_rfl
  norm_num [Nat.choose] at h
  exact ⟨h, by norm_num⟩

/-- EKL p. 42, "In particular, `X^{a,1}_{(1^a)} = 1`", is false for every `a ≥ 1`, even mod 2:
`X^{a,1}_{(1^a)}` is even. -/
theorem signX_col_self_even {a : ℕ} (ha : 1 ≤ a) : Even (signX a 1 (col a a)) := by
  have h := signX_col_mod_two ha le_rfl
  rw [Nat.sub_self, mul_zero, zero_add, Nat.choose_eq_zero_of_lt (by norm_num)] at h
  exact Nat.even_iff.mpr h

theorem signX_col_self_ne_one {a : ℕ} (ha : 1 ≤ a) : signX a 1 (col a a) ≠ 1 := by
  intro h
  have := signX_col_self_even ha
  rw [h] at this
  exact Nat.not_even_one this

/-- The sign `(−1)^{X^{a,1}_{(1^a)}}` is `+1`, not `−1`. -/
theorem neg_one_pow_signX_col_self {a : ℕ} (ha : 1 ≤ a) :
    (-1 : ℤ) ^ signX a 1 (col a a) = 1 :=
  (signX_col_self_even ha).neg_one_pow

/-! ## Prop 4.5 on the first `m` of `N ≥ m` variables -/

section Prop45
open OddMath.SkewPolynomial (SkewPolynomial monomial)
open LongestDivided PrefixEmbedding

/-- The `D_k` word of rank `N+3` is the `castSucc` image of the one of rank `N+2`. -/
theorem wordIn_succ (N k : ℕ) (h : k ≤ N+2) :
    wordIn (N+1) k (by omega) = (wordIn N k h).map Fin.castSucc := by
  apply List.map_injective_iff.mpr Fin.val_injective
  rw [wordIn_values, List.map_map]
  exact (wordIn_values N k h).symm

/-- Vanishing of `D_m` on a monomial transports to the first `m = n+2` of `N+2 ≥ m` variables,
whatever the exponents of the remaining variables. -/
theorem applyWord_prefix_eq_zero {n : ℕ} {γ : Fin (n+2) → ℕ} {c : ℤ}
    (h0 : D (n+2) (monomial γ c) = 0) (N : ℕ) (hN : n ≤ N) (η : Fin (N+2) → ℕ)
    (hη : ∀ i : Fin (n+2), η (Fin.castLE (by omega) i) = γ i) :
    applyWord (wordIn N (n+2) (by omega)) (monomial η c) = 0 := by
  induction N, hN using Nat.le_induction with
  | base =>
    have e : η = γ := funext fun i => by simpa using hη i
    subst e
    exact h0
  | succ N hN ih =>
    rw [wordIn_succ N (n+2) (by omega), ← Fin.snoc_init_self η, monomial_snoc,
      applyWord_map_castSucc]
    rw [ih (Fin.init η) fun i => by simpa [Fin.init] using hη i, map_zero]
    exact OddMath.SkewPolynomial.zero_mul _

/-- EKL Prop 4.5 (4.28) in rank `N+2 ≥ m`: for `a ≥ m = n+2` and `a−(m−1) ≤ p ≤ a−1`, the operator
`D_m` on the first `m` variables kills every monomial
`x_1^{a−1} ⋯ x_{m−1}^{a−(m−1)} x_m^p x_{m+1}^{η_{m+1}} ⋯ x_{N+2}^{η_{N+2}}`. -/
theorem prop_4_5_prefix (n a p : ℕ) (ham : n+2 ≤ a) (hp1 : a-(n+1) ≤ p) (hp2 : p ≤ a-1)
    (N : ℕ) (hN : n ≤ N) (η : Fin (N+2) → ℕ)
    (hη : ∀ i : Fin (n+2),
      η (Fin.castLE (by omega) i) =
        (Fin.snoc (fun i : Fin (n+1) => a-1-i.val) p : Fin (n+2) → ℕ) i) :
    applyWord (wordIn N (n+2) (by omega)) (monomial η 1) = 0 :=
  applyWord_prefix_eq_zero (StaircaseEvaluation.prop_4_5 n a p ham hp1 hp2) N hN η hη

/-- EKL Prop 4.5 (4.28) as printed, in `OPol_a`, `a = N+2`: `D_m` on the first `m = n+2` of the
`a` variables kills `x_1^{a−1} x_2^{a−2} ⋯ x_{m−1}^{a−(m−1)} x_m^p` for `a−(m−1) ≤ p ≤ a−1`. -/
theorem prop_4_5_rank (n N p : ℕ) (hN : n ≤ N) (hp1 : N+2-(n+1) ≤ p) (hp2 : p ≤ N+1) :
    applyWord (wordIn N (n+2) (by omega))
      (monomial (fun i : Fin (N+2) =>
        if i.val < n+1 then N+1-i.val else if i.val = n+1 then p else 0) 1) = 0 := by
  refine prop_4_5_prefix n (N+2) p (by omega) hp1 (by omega) N hN _ fun i => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  · simp only [Fin.coe_castLE, Fin.coe_castSucc, Fin.snoc_castSucc, i.isLt, if_true]
    omega

end Prop45

/-! ## (2.44): the graded rank of `ONH_a` as a Laurent series -/

section Rank244
open EKLSectionTwo (LS qpow qint qfactorial ofPS tsq qpow_add prod_qpow coeff_tsq tsq_X ofPS_X_pow)
open NilCoxeterWords (Perm length)
open PowerSeries

/-- `rk_q(ONH_a) = Σ_d rk(ONH_a)_d q^d`, `a = n+2`, from the degree pieces spanned by words in
dots (degree 2) and crossings (degree −2) (`NilHeckeGrading.degreePiece`). The degrees are
bounded below by `−2 max_w ℓ(w)`. -/
noncomputable def onhRank (n : ℕ) : LS where
  coeff d := (Module.finrank ℤ (NilHeckeGrading.degreePiece n d) : ℤ)
  isPWO_support' := by
    classical
    refine (BddBelow.isWF ⟨-2 * ((Finset.univ.sup fun w : Perm n => length w : ℕ) : ℤ),
      fun d hd => ?_⟩).isPWO
    rw [Function.mem_support, Nat.cast_ne_zero, NilHeckeGrading.degree_finrank_binomial] at hd
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
    have ha : NilHeckeGrading.admissible d w := by
      by_contra h; exact hw (if_neg h)
    have hle : length w ≤ Finset.univ.sup fun w : Perm n => length w :=
      Finset.le_sup (f := fun w : Perm n => length w) (Finset.mem_univ w)
    have := ha.1
    omega

theorem qpow_pow (k : ℤ) (m : ℕ) : qpow k ^ m = qpow (m * k) := by
  induction m with
  | zero => simp [EKLSectionTwo.qpow_zero]
  | succ m ih => rw [pow_succ, ih, ← qpow_add]; congr 1; push_cast; ring

/-- `Σ_{w ∈ S_a} q^{−2ℓ(w)} = q^{−a(a−1)/2} [a]!`. -/
theorem length_series_neg (n : ℕ) :
    ∑ w : Perm n, qpow (-2 * (length w : ℤ)) =
      qpow (-(((n+2).choose 2 : ℕ) : ℤ)) * qfactorial (n+2) := by
  have h := NilHeckeGradedEnd.schubert_physical_rank (qpow (-1)) n
  simp only [qpow_pow] at h
  rw [show (fun w : Perm n => qpow (-2 * (length w : ℤ))) =
      fun w => qpow (((2 * length w : ℕ) : ℤ) * -1) from funext fun w => by
        congr 1; push_cast; ring, h, qfactorial, ← prod_qpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [EKLSectionTwo.qint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← qpow_add]
  congr 1
  push_cast
  ring

/-- `1/(1 − q²)^a` as a Laurent series. -/
noncomputable def invOneSubSq (n : ℕ) : LS := ofPS (tsq (invOneSubPow ℤ (n+2)).val)

theorem invOneSubSq_mul (n : ℕ) : invOneSubSq n * (1 - qpow 2) ^ (n+2) = 1 := by
  have h := congrArg (fun f => ofPS (tsq f)) (invOneSubPow ℤ (n+2)).val_inv
  simp only [invOneSubPow_inv_eq_one_sub_pow] at h
  rw [map_mul, map_mul, map_pow, map_pow, map_sub, map_sub, map_one, map_one, tsq_X,
    ofPS_X_pow] at h
  exact h

theorem invOneSubSq_coeff (n : ℕ) (m : ℤ) :
    (invOneSubSq n).coeff m =
      if 0 ≤ m ∧ m % 2 = 0 then (((m / 2).toNat + n + 1).choose (n+1) : ℤ) else 0 := by
  rcases le_or_lt 0 m with hm | hm
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [invOneSubSq, HahnSeries.ofPowerSeries_apply_coeff, coeff_tsq,
      invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk]
    by_cases hk : Even k
    · rw [if_pos hk, if_pos ⟨hm, by obtain ⟨t, rfl⟩ := hk; omega⟩]
      congr 2
      omega
    · rw [if_neg hk, if_neg fun h => hk (Nat.even_iff.mpr (by omega))]
  · rw [if_neg (by omega), invOneSubSq, HahnSeries.ofPowerSeries_apply,
      HahnSeries.embDomain_notin_range]
    rintro ⟨k, hk⟩
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk] at hk
    omega

/-- EKL (2.44), p. 11, second line, for `a = n+2`:
`rk_q(ONH_a) = q^{−a(a−1)/2} [a]! · 1/(1 − q²)^a` in `ℤ((q))`. -/
theorem eq_2_44 (n : ℕ) :
    onhRank n = qpow (-(((n+2).choose 2 : ℕ) : ℤ)) * qfactorial (n+2) * invOneSubSq n := by
  rw [← length_series_neg, Finset.sum_mul]
  ext d
  rw [HahnSeries.coeff_sum]
  change (Module.finrank ℤ (NilHeckeGrading.degreePiece n d) : ℤ) = _
  rw [NilHeckeGrading.degree_finrank_binomial, Nat.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : d = (d + 2 * (length w : ℤ)) + (-2 * (length w : ℤ)) := by ring
  rw [qpow, e, HahnSeries.coeff_single_mul_add, one_mul, invOneSubSq_coeff, ← e]
  simp only [NilHeckeGrading.admissible, Nat.cast_ite, Nat.cast_zero]

/-- (2.44) multiplied out: `rk_q(ONH_a) (1 − q²)^a = q^{−a(a−1)/2} [a]!`. -/
theorem eq_2_44_mul (n : ℕ) :
    onhRank n * (1 - qpow 2) ^ (n+2) = qpow (-(((n+2).choose 2 : ℕ) : ℤ)) * qfactorial (n+2) := by
  rw [eq_2_44, mul_assoc, invOneSubSq_mul, mul_one]

end Rank244

end OddMath.Frontier.EKLMisc
