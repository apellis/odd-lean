import OddMath.Frontier.EKQuotientRelations
import OddMath.Frontier.EKSemiorthogonality
import OddMath.Frontier.EKCompleteErrata
import OddMath.Frontier.EKRestEval
import OddMath.Frontier.EKLSectionTwoG

/-!
# Errata in [EK], §§2–3: Proposition 2.11, the example after Proposition 2.14, (2.26),
# and the proof of Proposition 3.4

Source: A. P. Ellis, M. Khovanov, *The Hopf algebra of odd symmetric functions*,
arXiv:1107.5610v2. All statements concern the integral radical quotient `Λ = Q`
(`EKRadicalQuotient.Q`), its pairing `quotientPairing`, and the generators
`h_n = EKElementaryQuotient.h n`, `e_n = EKElementaryQuotient.e n`.

* **Proof of Prop. 2.11, p. 15, case `a + b` even.** The printed recurrence
  `(h_a e_b, e_k x) = (h_{a−k} e_b + (−1)^{b−k+1} h_{a−k+1} e_{b−1}, x)` tests against `e_k`;
  it fails for `a = b = k = 2`, `x = h_2`: the left side is `−2`, the right side `−1`
  (`prop_2_11_printed_even_instance`, `prop_2_11_printed_even_false`). With the test
  generator `h_k` the recurrence holds (`EKQuotientRelations.pairing_he_strip`), and at the
  same data both sides are `−1` (`prop_2_11_corrected_even_instance`).
* **Example after Prop. 2.14, p. 16.** For `λ = (4,4,2,1)` the number of strictly
  southwest–northeast pairs of boxes is `23`, not `22` (`ell_4421`, `ell_4421_ne_printed`),
  so `(h_λ, e_{λᵀ}) = −1` (`pairing_4421`).
* **Before (2.26), p. 21.** Applying the super anti-involution `ψ₃` to (2.5) does not
  produce (2.26) directly, since `ψ₃(e_k) = (−1)^{C(k+1,2)} ψ₂(e_k)` (`psi3_e`), which differs
  from `e_k` for `k ≥ 2`. What `ψ₃` gives is
  `Σ_k (−1)^{k(n−k)} h_{n−k} ψ₂(e_k) = 0` (`psi3_relation_2_5`); applying `ψ₂` in addition
  yields (2.26) (`eq_2_26`).
* **Proof of Prop. 3.4, pp. 25–26, `k = 5`, `m = 1`.** With the printed expansion of `p₅`
  (p. 25, verified in `p_five`), `(p₅h₁, e₃₃) = 2` and `(h₁p₅, e₃₃) = −2`, although
  `(3,3)` is neither `(k+1, 1^{m−1})` nor `(k, 1^m)` (`prop_3_4_support_false_k5`). The
  printed values at `(6)` and `(5,1)` hold for `k = 5` (`prop_3_4_values_k5`).
-/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace OddMath.Frontier.ErrataChecks
open EKRadicalQuotient EKMixedPairing EKPairingAdjoint EKQuotientRelations
open EKElementaryQuotient (h e)

/-! ## Proposition 2.11, p. 15 -/

private theorem word_two (a b : ℕ) (c d : Bool) : word ![a, b] ![c, d] = gen c a * gen d b := by
  simp [word, List.ofFn_succ]

private theorem pairing_gen_two (m a b : ℕ) (c d f : Bool) :
    EKPairingAdjoint.pairing (gen c a * gen d b) (gen f m) =
      if m = a + b then cell f c a * cell f d b else 0 := by
  rw [pairing_symm, ← word_two, pairing_gen_word]
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ]

private theorem h_eq_pi (n : ℕ) : h n = pi (gen false n) := rfl
private theorem e_eq_pi (n : ℕ) : e n = pi (gen true n) := rfl

/-- [EK] p. 15, proof of Prop. 2.11, `a + b` even, at `a = b = k = 2` and `x = h_2`:
`(h₂e₂, e₂h₂) = −2`, while the printed right-hand side
`(h₀e₂ + (−1)^{b−k+1} h₁e₁, h₂)` equals `−1`. -/
theorem prop_2_11_printed_even_instance :
    quotientPairing (h 2 * e 2) (e 2 * h 2) = -2 ∧
    quotientPairing (h (2-2) * e 2 + (-1 : ℤ)^(2-2+1) • (h (2-2+1) * e (2-1))) (h 2) = -1 := by
  simp only [h_eq_pi, e_eq_pi, ← map_mul, ← map_zsmul, ← map_add, quotientPairing_pi]
  constructor
  · rw [pairing_two_strip]
    simp [Fin.sum_univ_succ, pairing_gen_two, pairing_gen_self, cell]
  · simp [pairing_gen_two, cell, gen_zero, pairing_gen_self]

/-- [EK] p. 15, proof of Prop. 2.11: the printed even-case recurrence with test generator
`e_k` is false. -/
theorem prop_2_11_printed_even_false :
    ¬ ∀ a b k : ℕ, Even (a + b) → 1 ≤ k → k ≤ a → k ≤ b → ∀ x : Q,
      quotientPairing (h a * e b) (e k * x) =
        quotientPairing (h (a-k) * e b + (-1 : ℤ)^(b-k+1) • (h (a-k+1) * e (b-1))) x := by
  intro hall
  have h1 := hall 2 2 2 (by decide) (by decide) le_rfl le_rfl (h 2)
  obtain ⟨hl, hr⟩ := prop_2_11_printed_even_instance
  rw [hl, hr] at h1
  norm_num at h1

/-- [EK] p. 15, proof of Prop. 2.11, corrected (test generator `h_k`), at the same data:
`(h₂e₂, h₂h₂) = (h₀e₂ + (−1)^{a−k+1} h₁e₁, h₂) = −1`. The general recurrence is
`EKQuotientRelations.pairing_he_strip`. -/
theorem prop_2_11_corrected_even_instance :
    quotientPairing (h 2 * e 2) (h 2 * h 2) =
      quotientPairing (h (2-2) * e 2 + (-1 : ℤ)^(2-2+1) • (h (2-2+1) * e (2-1))) (h 2) ∧
    quotientPairing (h 2 * e 2) (h 2 * h 2) = -1 := by
  have hc : quotientPairing (h 2 * e 2) (h 2 * h 2) = -1 := by
    simp only [h_eq_pi, e_eq_pi, ← map_mul, quotientPairing_pi]
    have hh := pairing_he_strip 2 1 1 (gen false 2)
    rw [hh]
    simp [pairing_gen_two, cell, gen_zero, pairing_gen_self]
  refine ⟨?_, hc⟩
  rw [hc, prop_2_11_printed_even_instance.2]

/-! ## Example after Proposition 2.14, p. 16 -/

/-- The partition `(4,4,2,1)`. -/
def shape4421 : YoungDiagram := YoungDiagram.ofRowLens [4, 4, 2, 1] (by decide)

/-- [EK] p. 16: `ℓ(w_{(4,4,2,1)}) = 23`, counted as strictly southwest–northeast pairs of boxes
(`EKSemiorthogonality.ell`), with row labels `0,0,0,0 / 3,2,1,0 / 6,4 / 7`. -/
theorem ell_4421 : EKSemiorthogonality.ell shape4421 = 23 := by decide

/-- [EK] p. 16: the printed value `ℓ(w_{(4,4,2,1)}) = 22` is wrong. -/
theorem ell_4421_ne_printed : EKSemiorthogonality.ell shape4421 ≠ 22 := by
  rw [ell_4421]; decide

/-- [EK] (2.20) at `λ = (4,4,2,1)`: `(h_λ, e_{λᵀ}) = (−1)^{23} = −1`; the printed count `22`
would give `+1`. -/
theorem pairing_4421 :
    quotientPairing (EKSemiorthogonality.hPartition shape4421)
      (EKSemiorthogonality.ePartition shape4421.transpose) = -1 ∧
    quotientPairing (EKSemiorthogonality.hPartition shape4421)
      (EKSemiorthogonality.ePartition shape4421.transpose) ≠ (-1 : ℤ)^22 := by
  rw [EKSemiorthogonality.proposition_2_14_diagonal, ell_4421]
  norm_num

/-! ## The step before (2.26), p. 21 -/

open EKAutomorphisms (psi2 psi3 s reverseLinear)

/-- The ordinary anti-involution `R` of `Λ` fixing every `h_n` commutes with `ψ₂`. -/
theorem reverse_psi2 (x : Q) : reverseLinear (psi2 x) = psi2 (reverseLinear x) := by
  induction x using EKPairingAdjoint.basis_induction EKIntegralBases.hBasis with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx, hy]
  | hb μ r =>
    have hp : EKIntegralBases.hBasis μ = (μ.rowLens.map h).prod := by
      rw [EKIntegralBases.hBasis_apply]; rfl
    rw [hp]
    simp only [map_zsmul, EKAutomorphisms.psi2_word, EKAutomorphisms.reverse_word,
      EKAutomorphisms.wordSign_reverse]

/-- `ψ₃(e_n) = (−1)^{C(n+1,2)} ψ₂(e_n)` ([EK] §2.3). In particular `ψ₃` does not fix `e_n`
for `n ≥ 2` (`EKComplete.psi3_e_ne`). -/
theorem psi3_e (n : ℕ) : psi3 (e n) = s n • psi2 (e n) := by
  rw [EKAutomorphisms.psi3_homogeneous (EKComplete.e_mem n), reverse_psi2,
    EKLSectionTwo.reverse_e]

/-- [EK] p. 21: the result of applying `ψ₃` to (2.5), for `n ≥ 1`:
`Σ_{k=0}^{n} (−1)^{k(n−k)} h_{n−k} ψ₂(e_k) = 0`. -/
theorem psi3_relation_2_5 (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (n+1), (-1 : ℤ)^(k*(n-k)) • (h (n-k) * psi2 (e k)) = 0 := by
  have h1 := congrArg psi3 (EKComplete.relation_2_5 n hn)
  rw [map_sum, map_zero] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, EKAutomorphisms.psi3_mul (EKComplete.e_mem k) (EKComplete.h_mem (n-k)),
    EKAutomorphisms.psi3_h, psi3_e, smul_smul, mul_smul_comm, smul_smul]
  congr 1
  have := EKAutomorphisms.s_square k
  calc (-1 : ℤ)^(k*(n-k)) = s k * ((-1 : ℤ)^(k*(n-k)) * s k) := by
        rw [mul_comm ((-1 : ℤ)^(k*(n-k))), ← mul_assoc, this, one_mul]
    _ = _ := by ring

/-- [EK] (2.26), p. 21, obtained from (2.5) by applying `ψ₂ψ₃` (not `ψ₃` alone), for `n ≥ 1`:
`Σ_{k=0}^{n} (−1)^{C(k+1,2)} h_{n−k} e_k = 0`. -/
theorem eq_2_26 (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (n+1), s k • (h (n-k) * e k) = 0 := by
  have h1 := congrArg psi2 (psi3_relation_2_5 n hn)
  rw [map_sum, map_zero] at h1
  have h2 : ∑ k ∈ Finset.range (n+1), s n • (s k • (h (n-k) * e k)) = 0 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [map_zsmul, map_mul, EKAutomorphisms.psi2_h, EKAutomorphisms.psi2_involutive,
      smul_smul, smul_mul_assoc, smul_smul]
    congr 1
    have hs := EKAutomorphisms.s_add k (n-k)
    rw [Nat.add_sub_cancel' hk'] at hs
    rw [hs]
    have h3 := EKAutomorphisms.s_square k
    calc s k * s (n-k) * (-1 : ℤ)^(k*(n-k)) * s k
        = (s k * s k) * (s (n-k) * (-1 : ℤ)^(k*(n-k))) := by ring
      _ = _ := by rw [h3, one_mul, mul_comm]
  rw [← Finset.smul_sum] at h2
  have h3 := congrArg (fun x : Q => s n • x) h2
  simpa only [smul_smul, EKAutomorphisms.s_square, one_smul, smul_zero] using h3

/-! ## Proof of Proposition 3.4, pp. 25–26, `k = 5` -/

open EKComplete EKNondegeneracy EKRest

private theorem hL_col (l : List ℕ) : hL l = (l.map (col false)).prod := by
  rw [hL]; congr 2

private theorem eL_col (l : List ℕ) : eL l = (l.map (col true)).prod := by
  rw [eL]; congr 2

private theorem pairing_hL_hL_fast (l l' : List ℕ) :
    quotientPairing (hL l) (hL l') = fastH l l' := by
  rw [hL_col, hL_col, pairing_const, fastH]

private theorem pairing_hL_eL_fast (l l' : List ℕ) :
    quotientPairing (hL l) (eL l') =
      fastEval l (List.replicate l.length false) l' (List.replicate l'.length true) := by
  rw [hL_col, eL_col, pairing_const]

private theorem pair_hL_comb_fast (l : List ℕ) (c : List (ℤ × List ℕ)) :
    quotientPairing (hL l) (comb c) = (c.map fun t => t.1 * fastH l t.2).sum := by
  induction c with
  | nil => simp [comb]
  | cons t c ih =>
    simp only [comb, List.map_cons, List.sum_cons, map_add, map_zsmul, smul_eq_mul] at ih ⊢
    rw [ih, pairing_hL_hL_fast]

private theorem pair_comb_eL_fast (c : List (ℤ × List ℕ)) (l : List ℕ) :
    quotientPairing (comb c) (eL l) = (c.map fun t => t.1 *
      fastEval t.2 (List.replicate t.2.length false) l (List.replicate l.length true)).sum := by
  induction c with
  | nil => simp [comb]
  | cons t c ih =>
    simp only [comb, List.map_cons, List.sum_cons, map_add, map_zsmul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul] at ih ⊢
    rw [ih, pairing_hL_eL_fast]

/-- The printed expansion of `p₅` ([EK] p. 25):
`p₅ = h₁₁₁₁₁ + h₂₁₁₁ + 3h₂₂₁ − h₃₁₁ − 3h₃₂ − 9h₄₁ + 9h₅`. -/
def P5 : List (ℤ × List ℕ) :=
  [(1, [1, 1, 1, 1, 1]), (1, [2, 1, 1, 1]), (3, [2, 2, 1]), (-1, [3, 1, 1]), (-3, [3, 2]),
    (-9, [4, 1]), (9, [5])]

/-- [EK] p. 25: the printed expansion of `p₅ = m₅` holds. -/
theorem p_five : EKCenterPower.p 5 = comb P5 := by
  refine eq_of_pair_hL (p_mem 5) (comb_mem 5 P5 (by decide)) fun l hl => ?_
  have hshape : ∀ l ∈ partsF 5 5 5, l.Sorted (· ≥ ·) ∧ ∀ x ∈ l, 0 < x := by decide
  have hval : ∀ l ∈ partsF 5 5 5,
      (P5.map fun t => t.1 * fastH l t.2).sum = if l = [5] then 1 else 0 := by decide +kernel
  rw [pair_hL_comb_fast, hval l hl, pair_hL_p (by decide) l (hshape l hl).1 (hshape l hl).2]

/-- [EK] proof of Prop. 3.4, pp. 25–26, `k = 5`, `m = 1`: the support claim fails at
`λ = (3,3)`, which is neither `(k+1, 1^{m−1}) = (6)` nor `(k, 1^m) = (5,1)`:
`(p₅h₁, e₃₃) = 2` and `(h₁p₅, e₃₃) = −2`. -/
theorem prop_3_4_support_false_k5 :
    quotientPairing (EKCenterPower.p 5 * h 1) (eL [3, 3]) = 2 ∧
    quotientPairing (h 1 * EKCenterPower.p 5) (eL [3, 3]) = -2 := by
  rw [p_five, comb_mul_h, h_mul_comb, pair_comb_eL_fast, pair_comb_eL_fast]
  decide +kernel

/-- [EK] proof of Prop. 3.4, `k = 5`, `m = 1`: the printed values
`(p_k h_m, e_{k+1}e_1^{m−1}) = 1`, `(h_m p_k, e_{k+1}e_1^{m−1}) = (−1)^{k(m−1)}`,
`(p_k h_m, e_k e_1^m) = 1`, `(h_m p_k, e_k e_1^m) = (−1)^{km}` hold. -/
theorem prop_3_4_values_k5 :
    quotientPairing (EKCenterPower.p 5 * h 1) (eL [6]) = 1 ∧
    quotientPairing (h 1 * EKCenterPower.p 5) (eL [6]) = (-1 : ℤ)^(5*(1-1)) ∧
    quotientPairing (EKCenterPower.p 5 * h 1) (eL [5, 1]) = 1 ∧
    quotientPairing (h 1 * EKCenterPower.p 5) (eL [5, 1]) = (-1 : ℤ)^(5*1) := by
  rw [p_five, comb_mul_h, h_mul_comb, pair_comb_eL_fast, pair_comb_eL_fast, pair_comb_eL_fast,
    pair_comb_eL_fast]
  decide +kernel

end OddMath.Frontier.ErrataChecks
