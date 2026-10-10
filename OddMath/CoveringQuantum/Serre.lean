/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Module
import OddMath.CoveringQuantum.HalfAlgebra

/-!
# The quantum Serre relations hold in `'f / I`

Clark–Hill–Wang, arXiv:1301.1665v2 ([CHW1]), Prop. 1.7.3: the quantum Serre relations hold in
`f = 'f / I`. We prove this for the relations (10.1) of Brundan–Ellis, arXiv:1701.04133v2
([BE2]), §10, written without divided powers, with [BE2]'s twist and for an arbitrary
normalization `(θᵢ, θᵢ)`: the left side `S` of (10.1) satisfies `rₖ(S) = 0` in `'f` for all `k`,
hence lies in the radical ([CHW1] Lemma 1.5.2, `PreF.mem_radical_of_rDeriv_mem`). Consequently
[BE2]'s `f` (`SuperCartanDatum.serreF`) maps onto [CHW1]'s `f` (`SuperCartanDatum.radicalF`).

The scalar identities used are the absorption identity `[t+1][N, t+1] = [N-t][N, t]` and the
`(q, π)`-binomial theorem `Σₜ π^{t(t-1)/2} q^{-tN} [N+1, t] zᵗ = ∏_{j ≤ N} (1 + πʲ q^{-2j} z)`
(cf. [CHW1] (1.12), in [BE2]'s convention `q ↦ q⁻¹`), from which
`Σₜ (-1)ᵗ π^{t(t-1)/2} q^{t(N-1)} [N, t] = 0` for `N ≥ 1` odd or `π = 1` (cf. [CHW1] (1.15));
this is the identity used in [CHW1] §1.7.5, where `N` is odd whenever `i` is odd, by
[CHW1] §1.1 (d).

## Main results

* `OddMath.CoveringQuantum.qpNat_mul_qpBinom`: `[t+1][N, t+1] = [N-t][N, t]`.
* `OddMath.CoveringQuantum.qpBinom_prod`: the `(q, π)`-binomial theorem.
* `OddMath.CoveringQuantum.alternating_qpBinom_eq_zero`.
* `OddMath.CoveringQuantum.PreF.rDeriv_θ_pow`, `PreF.rDeriv_serreWord`: `rₖ` on `θᵢᵃ θⱼ θᵢᵇ`.
* `SuperCartanDatum.rDeriv_serreElt`: `rₖ(S) = 0`.
* `SuperCartanDatum.serreElt_mem_radical`: `S` lies in the radical of the form.
* `SuperCartanDatum.serreToRadical`: the surjection from [BE2]'s `f` onto [CHW1]'s `f`.
-/

noncomputable section

namespace OddMath.CoveringQuantum

open Finset

/-! ### Scalar identities -/

section Scalars

variable {k : Type*} [CommRing k] {q : kˣ} {π : k}

local notation "Q" => ((q : kˣ) : k)
local notation "Qi" => ((q⁻¹ : kˣ) : k)

/-- The absorption identity `[t+1] [N, t+1] = [N-t] [N, t]`. -/
theorem qpNat_mul_qpBinom (N t : ℕ) :
    qpNat q π (t + 1) * qpBinom q π N (t + 1) = qpNat q π (N - t) * qpBinom q π N t := by
  induction N generalizing t with
  | zero => simp
  | succ N ih =>
    rcases t with _ | s
    · simp [qpBinom_one_right]
    rcases Nat.lt_or_ge s N with hs | hs
    · obtain ⟨m, rfl⟩ : ∃ m, N = s + 1 + m := ⟨N - (s + 1), by omega⟩
      have sp2 : qpBinom q π (s + 1 + m + 1) (s + 1 + 1) = Q ^ (s + 1 + 1) *
          qpBinom q π (s + 1 + m) (s + 1 + 1) + π ^ m * Qi ^ m * qpBinom q π (s + 1 + m) (s + 1) := by
        rw [qpBinom_succ_succ', show s + 1 + m - (s + 1) = m by omega]
      have fp1 : qpBinom q π (s + 1 + m + 1) (s + 1) = π ^ (s + 1) * Qi ^ (s + 1) *
          qpBinom q π (s + 1 + m) (s + 1) + Q ^ (m + 1) * qpBinom q π (s + 1 + m) s := by
        rw [qpBinom_succ_succ, show s + 1 + m - s = m + 1 by omega]
      have ih1 := ih (s + 1)
      rw [show s + 1 + m - (s + 1) = m by omega] at ih1
      have ih2 := ih s
      rw [show s + 1 + m - s = m + 1 by omega] at ih2
      have hA := qpNat_add (q := q) (π := π) (s + 1 + 1) m
      have hB := qpNat_add (q := q) (π := π) (m + 1) (s + 1)
      rw [show s + 1 + 1 + m = s + 1 + m + 1 by omega] at hA
      rw [show m + 1 + (s + 1) = s + 1 + m + 1 by omega] at hB
      rw [show s + 1 + m + 1 - (s + 1) = m + 1 by omega]
      linear_combination qpNat q π (s + 1 + 1) * sp2 - qpNat q π (m + 1) * fp1 +
        Q ^ (s + 1 + 1) * ih1 + Q ^ (m + 1) * ih2 -
        qpBinom q π (s + 1 + m) (s + 1) * (hA - hB)
    · rw [qpBinom_eq_zero_of_lt (by omega : N + 1 < s + 1 + 1),
        show N + 1 - (s + 1) = 0 by omega, qpNat_zero]
      ring

/-- The `(q, π)`-binomial theorem
`Σ_{t=0}^{N+1} π^{t(t-1)/2} q^{-tN} [N+1, t] zᵗ = ∏_{j=0}^{N} (1 + πʲ q^{-2j} z)`
(cf. [CHW1] (1.12), with `q ↦ q⁻¹`). -/
theorem qpBinom_prod (N : ℕ) (z : k) :
    ∑ t ∈ range (N + 2), π ^ t.choose 2 * Qi ^ (t * N) * qpBinom q π (N + 1) t * z ^ t =
      ∏ j ∈ range (N + 1), (1 + π ^ j * Qi ^ (2 * j) * z) := by
  have hqq : Qi * Q = 1 := q.inv_mul
  induction N with
  | zero =>
    simp [sum_range_succ]
  | succ N ih =>
    have key : ∀ t ∈ range (N + 2),
        π ^ (t + 1).choose 2 * Qi ^ ((t + 1) * (N + 1)) * qpBinom q π (N + 1 + 1) (t + 1) *
          z ^ (t + 1) =
        π ^ (t + 1).choose 2 * Qi ^ ((t + 1) * N) * qpBinom q π (N + 1) (t + 1) * z ^ (t + 1) +
        π ^ t.choose 2 * Qi ^ (t * N) * qpBinom q π (N + 1) t * z ^ t *
          (π ^ (N + 1) * Qi ^ (2 * (N + 1)) * z) := by
      intro t ht
      have ht := mem_range.1 ht
      obtain ⟨m, hm⟩ : ∃ m, N + 1 - t = m := ⟨_, rfl⟩
      have htm : t + m = N + 1 := by omega
      have hc : (t + 1).choose 2 = t.choose 2 + t := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
      rw [qpBinom_succ_succ', hm, hc]
      have e1 : Qi ^ ((t + 1) * (N + 1)) * Q ^ (t + 1) = Qi ^ ((t + 1) * N) := by
        rw [show (t + 1) * (N + 1) = (t + 1) * N + (t + 1) by ring, pow_add, mul_assoc, ← mul_pow,
          hqq, one_pow, mul_one]
      have e4 : π ^ (t.choose 2 + t) * π ^ m = π ^ t.choose 2 * π ^ (N + 1) := by
        rw [← pow_add, ← pow_add, add_assoc, htm]
      have e5 : Qi ^ ((t + 1) * (N + 1)) * Qi ^ m = Qi ^ (t * N) * Qi ^ (2 * (N + 1)) := by
        rw [← pow_add, ← pow_add]
        congr 1
        nlinarith [htm]
      linear_combination (qpBinom q π (N + 1) (t + 1) * z ^ (t + 1) * π ^ (t.choose 2 + t)) * e1 +
        (qpBinom q π (N + 1) t * z ^ (t + 1)) *
          (Qi ^ (t * N) * Qi ^ (2 * (N + 1)) * e4 + π ^ (t.choose 2 + t) * π ^ m * e5)
    have h2 := sum_range_succ'
      (fun t ↦ π ^ t.choose 2 * Qi ^ (t * N) * qpBinom q π (N + 1) t * z ^ t) (N + 2)
    have h3 := sum_range_succ
      (fun t ↦ π ^ t.choose 2 * Qi ^ (t * N) * qpBinom q π (N + 1) t * z ^ t) (N + 2)
    rw [qpBinom_eq_zero_of_lt (by omega : N + 1 < N + 2)] at h3
    simp only [zero_mul, pow_zero, qpBinom_zero_right, mul_one, mul_zero, add_zero] at h2 h3
    rw [prod_range_succ, ← ih, sum_range_succ' _ (N + 2), sum_congr rfl key, sum_add_distrib,
      ← sum_mul]
    simp only [zero_mul, pow_zero, qpBinom_zero_right, mul_one]
    have h0 : (0 : ℕ).choose 2 = 0 := rfl
    rw [h0, pow_zero] at h2 ⊢
    linear_combination -(h3.symm.trans h2)

/-- `Σₜ (-1)ᵗ π^{t(t-1)/2} q^{t(N-1)} [N, t] = 0` for `N ≥ 1` odd, given `π² = 1`; and for all
`N ≥ 1` when `π = 1`. -/
theorem alternating_qpBinom_eq_zero (hπ : π ^ 2 = 1) {N : ℕ} (hN : 1 ≤ N)
    (hodd : Odd N ∨ π = 1) :
    ∑ t ∈ range (N + 1), (-1) ^ t * π ^ t.choose 2 * Q ^ (t * (N - 1)) * qpBinom q π N t = 0 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h := qpBinom_prod (q := q⁻¹) (π := π) M (-1)
  rw [prod_range_succ'] at h
  simp only [pow_zero, mul_zero, one_mul, add_neg_cancel, inv_inv] at h
  rw [Nat.add_sub_cancel, ← h]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [qpBinom_inv hπ]
  have : π ^ (t * (M + 1 - t)) = 1 := by
    rcases hodd with hodd | rfl
    · have hev : Even (t * (M + 1 - t)) := by
        rcases Nat.even_or_odd t with ht' | ht'
        · exact ht'.mul_right _
        · exact (Nat.Odd.sub_odd hodd ht').mul_left _
      obtain ⟨r, hr⟩ := hev
      rw [hr, ← two_mul, pow_mul, hπ, one_pow]
    · exact one_pow _
  rw [this, one_mul]
  ring

end Scalars

/-! ### `rₖ` on the words `θᵢᵃ θⱼ θᵢᵇ` -/

namespace PreF

variable {k I : Type*} [CommRing k] (χ : Bichar k I)

/-- `rₖ(θᵢᵐ) = δₖᵢ (Σ_{s<m} χ(i,i)ˢ) θᵢ^{m-1}`. -/
theorem rDeriv_θ_pow [DecidableEq I] (i l : I) (m : ℕ) :
    rDeriv χ l (θ k i ^ m) =
      if l = i then (∑ s ∈ range m, χ i i ^ s) • θ k i ^ (m - 1) else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, rDeriv_mul, ih, rDeriv_θ, twist_θ]
    split_ifs with h
    · subst h
      rw [mul_one, smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_succ]
      rcases m with _ | n
      · simp
      · rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
        conv_lhs => arg 1; rw [← one_smul k (θ k l ^ (n + 1))]
        rw [← add_smul, sum_range_succ' _ (n + 1), sum_mul, pow_zero, add_comm]
        congr 2
        exact sum_congr rfl fun s _ ↦ (pow_succ _ _).symm
    · simp

/-- `rₖ(θᵢᵃ θⱼ θᵢᵇ)` for `i ≠ j`: for `k = i` it is
`(Σ_{s<b} χ(i,i)ˢ) θᵢᵃ θⱼ θᵢ^{b-1} + (Σ_{s<a} χ(i,i)ˢ) χ(i,j) χ(i,i)ᵇ θᵢ^{a-1} θⱼ θᵢᵇ`, for `k = j`
it is `χ(j,i)ᵇ θᵢ^{a+b}`, and it vanishes otherwise. -/
theorem rDeriv_serreWord [DecidableEq I] {i j : I} (hij : i ≠ j) (l : I) (a b : ℕ) :
    rDeriv χ l (θ k i ^ a * θ k j * θ k i ^ b) =
      (if l = i then (∑ s ∈ range b, χ i i ^ s) • (θ k i ^ a * θ k j * θ k i ^ (b - 1)) +
          ((∑ s ∈ range a, χ i i ^ s) * χ i j * χ i i ^ b) • (θ k i ^ (a - 1) * θ k j * θ k i ^ b)
        else 0) +
      (if l = j then χ j i ^ b • θ k i ^ (a + b) else 0) := by
  have htw : twist χ l (θ k i ^ b) = χ l i ^ b • θ k i ^ b := by
    rw [map_pow, twist_θ, smul_pow]
  rw [rDeriv_mul, rDeriv_mul, rDeriv_θ_pow, rDeriv_θ_pow, rDeriv_θ, htw, twist_θ]
  by_cases hli : l = i
  · subst hli
    simp only [↓reduceIte, hij, mul_zero, zero_add, add_zero]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
    module
  · by_cases hlj : l = j
    · subst hlj
      simp only [↓reduceIte, hli, mul_one, mul_zero, zero_mul, add_zero, zero_add]
      rw [mul_smul_comm, ← pow_add]
    · simp [hli, hlj]

end PreF

/-! ### The covering case -/

section CoveringScalars

variable {k : Type*} [CommRing k]

/-- `(Σ_{s ≤ m} (q⁻² π)ˢ) qᵐ = [m+1]_{q,π}`. -/
theorem geom_mul_pow_eq_qpNat (u : kˣ) (ε : k) (m : ℕ) :
    (∑ s ∈ range (m + 1), (((u⁻¹ : kˣ) : k) ^ 2 * ε) ^ s) * (u : k) ^ m = qpNat u ε (m + 1) := by
  have hu : ((u⁻¹ : kˣ) : k) * u = 1 := u.inv_mul
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ', qpNat_succ (q := u) (π := ε) (m + 1), ← ih]
    have hs : ∑ s ∈ range (m + 1), (((u⁻¹ : kˣ) : k) ^ 2 * ε) ^ (s + 1) =
        (∑ s ∈ range (m + 1), (((u⁻¹ : kˣ) : k) ^ 2 * ε) ^ s) * (((u⁻¹ : kˣ) : k) ^ 2 * ε) := by
      rw [sum_mul]; exact sum_congr rfl fun _ _ ↦ pow_succ _ _
    rw [hs]
    linear_combination ((∑ s ∈ range (m + 1), (((u⁻¹ : kˣ) : k) ^ 2 * ε) ^ s) * (u : k) ^ m * ε *
      ((u⁻¹ : kˣ) : k)) * hu

/-- The coefficient identity behind `rᵢ(S) = 0`, with `N = t + 1 + m`. -/
theorem serre_coeff_rel (u : kˣ) (ε : k) (e t m : ℕ) :
    (-1) ^ (t + 1) * ε ^ ((t + 1) * e + (t + 1).choose 2) * qpBinom u ε (t + 1 + m) (t + 1) *
        ∑ s ∈ range (t + 1), (((u⁻¹ : kˣ) : k) ^ 2 * ε) ^ s +
      (-1) ^ t * ε ^ (t * e + t.choose 2) * qpBinom u ε (t + 1 + m) t *
        ((∑ s ∈ range (t + 1 + m - t), (((u⁻¹ : kˣ) : k) ^ 2 * ε) ^ s) *
          ((u : k) ^ (t + 1 + m - 1) * ε ^ e) * (((u⁻¹ : kˣ) : k) ^ 2 * ε) ^ t) = 0 := by
  have hu : ((u⁻¹ : kˣ) : k) * u = 1 := u.inv_mul
  have hut : (((u⁻¹ : kˣ) : k) * u) ^ t = 1 := by rw [hu, one_pow]
  have hc : (t + 1).choose 2 = t.choose 2 + t := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
  rw [show t + 1 + m - t = m + 1 by omega, show t + 1 + m - 1 = t + m by omega, hc]
  set G₁ := ∑ s ∈ range (t + 1), (((u⁻¹ : kˣ) : k) ^ 2 * ε) ^ s
  set G₂ := ∑ s ∈ range (m + 1), (((u⁻¹ : kˣ) : k) ^ 2 * ε) ^ s
  have h1 : G₁ * (u : k) ^ t = qpNat u ε (t + 1) := geom_mul_pow_eq_qpNat u ε t
  have h2 : G₂ * (u : k) ^ m = qpNat u ε (m + 1) := geom_mul_pow_eq_qpNat u ε m
  have h1' : G₁ = ((u⁻¹ : kˣ) : k) ^ t * qpNat u ε (t + 1) := by
    rw [← h1]; linear_combination (-G₁) * hut
  have h2' : G₂ * (u : k) ^ (t + m) * ((u⁻¹ : kˣ) : k) ^ (2 * t) =
      ((u⁻¹ : kˣ) : k) ^ t * qpNat u ε (m + 1) := by
    linear_combination ((u⁻¹ : kˣ) : k) ^ t * h2 + (G₂ * (u : k) ^ m * ((u⁻¹ : kˣ) : k) ^ t) * hut
  have hA := qpNat_mul_qpBinom (q := u) (π := ε) (t + 1 + m) t
  rw [show t + 1 + m - t = m + 1 by omega] at hA
  linear_combination
    (-((-1) ^ t * ε ^ ((t + 1) * e + (t.choose 2 + t)) * qpBinom u ε (t + 1 + m) (t + 1))) * h1' +
    ((-1) ^ t * ε ^ (t * e + t.choose 2) * qpBinom u ε (t + 1 + m) t * ε ^ e * ε ^ t) * h2' -
    ((-1) ^ t * ε ^ ((t + 1) * e + (t.choose 2 + t)) * ((u⁻¹ : kˣ) : k) ^ t) * hA

/-- The coefficient identity behind `rⱼ(S) = 0`. -/
theorem serre_coeff_sum (u : kˣ) {ε : k} (hε : ε ^ 2 = 1) (e : ℕ) {N : ℕ} (hN : 1 ≤ N)
    (hodd : Odd N ∨ ε = 1) :
    ∑ r ∈ range (N + 1), (-1) ^ r * ε ^ (r * e + r.choose 2) * qpBinom u ε N r *
      ((u : k) ^ (N - 1) * ε ^ e) ^ r = 0 := by
  rw [← alternating_qpBinom_eq_zero (q := u) hε hN hodd]
  refine sum_congr rfl fun r _ ↦ ?_
  have : ε ^ (r * e) * ε ^ (r * e) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, hε, one_pow]
  linear_combination ((-1) ^ r * ε ^ r.choose 2 * qpBinom u ε N r * (u : k) ^ (r * (N - 1))) * this

end CoveringScalars

namespace SuperCartanDatum

variable {I k : Type*} [CommRing k] (C : SuperCartanDatum I) (q : kˣ) (π : k)

private lemma zmod2_val_mul (a b : ZMod 2) : (a * b).val = a.val * b.val := by
  fin_cases a <;> fin_cases b <;> rfl

theorem chi_self (i : I) :
    C.chi q π i i = (((C.qi q i)⁻¹ : kˣ) : k) ^ 2 * C.pii π i := by
  rw [chi_apply, pii, zmod2_val_mul, C.dot_self]
  have hq : q ^ (-(2 * (C.d i : ℤ))) = (C.qi q i)⁻¹ ^ 2 := by
    rw [qi, inv_pow, ← pow_mul, ← zpow_natCast, ← zpow_neg]
    push_cast; ring_nf
  rw [hq, Units.val_pow_eq_pow_val]
  have hp : (C.parity i).val * (C.parity i).val = (C.parity i).val := by
    have := ZMod.val_lt (C.parity i)
    interval_cases (C.parity i).val <;> rfl
  rw [hp]

theorem serreDeg_eq {i j : I} (h : i ≠ j) : (C.serreDeg i j : ℤ) = 1 - C.a i j := by
  have := C.isGCM.offDiag_nonpos i j h
  rw [serreDeg, Int.toNat_of_nonneg (by omega)]

theorem chi_of_ne {i j : I} (h : i ≠ j) :
    C.chi q π i j = ((C.qi q i : kˣ) : k) ^ (C.serreDeg i j - 1) * C.pii π i ^ (C.parity j).val := by
  have hN := C.serreDeg_eq h
  have hd : -C.dot i j = ((C.d i * (C.serreDeg i j - 1) : ℕ) : ℤ) := by
    have h1 : 1 ≤ C.serreDeg i j := by have := C.isGCM.offDiag_nonpos i j h; omega
    rw [dot]; push_cast [h1]; rw [hN]; ring
  rw [chi_apply, hd, zpow_natCast, pow_mul, Units.val_pow_eq_pow_val, pii, ← pow_mul,
    zmod2_val_mul]
  rfl

theorem pii_sq (hπ : π ^ 2 = 1) (i : I) : C.pii π i ^ 2 = 1 := by
  rw [pii, ← pow_mul, mul_comm, pow_mul, hπ, one_pow]

theorem odd_serreDeg_or {i j : I} (h : i ≠ j) : Odd (C.serreDeg i j) ∨ C.pii π i = 1 := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (C.parity i) with hp | hp
  · right
    rw [pii, hp, ZMod.val_zero, pow_zero]
  · left
    obtain ⟨n, hn⟩ := C.even_of_odd i j hp
    have h1 := C.serreDeg_eq h
    have h2 := C.isGCM.offDiag_nonpos i j h
    exact ⟨(-n).toNat, by omega⟩

end SuperCartanDatum

/-! ### The Serre relations lie in the radical -/

namespace SuperCartanDatum

variable {I k : Type*} [CommRing k] [DecidableEq I] (C : SuperCartanDatum I) (q : kˣ) (π : k)

omit [DecidableEq I] in
theorem counit_serreElt (i j : I) : PreF.counit (C.serreElt q π i j) = 0 := by
  simp [serreElt, map_sum]

/-- `rₖ(S) = 0` in `'f` for the left side `S` of the quantum Serre relation (10.1) and every `k`
(cf. the proof of [CHW1] Prop. 1.7.3), given `π² = 1`. -/
theorem rDeriv_serreElt (hπ : π ^ 2 = 1) {i j : I} (hij : i ≠ j) (l : I) :
    PreF.rDeriv (C.chi q π) l (C.serreElt q π i j) = 0 := by
  have hN1 : 1 ≤ C.serreDeg i j := by
    have := C.serreDeg_eq hij; have := C.isGCM.offDiag_nonpos i j hij; omega
  simp only [serreElt, map_sum, map_smul, PreF.rDeriv_serreWord _ hij]
  by_cases hli : l = i
  · subst l
    simp only [↓reduceIte, hij, add_zero, smul_add, sum_add_distrib, smul_smul]
    rw [sum_range_succ', sum_range_succ]
    simp only [Nat.sub_self, sum_range_zero, zero_mul, mul_zero, zero_smul, add_zero]
    rw [← sum_add_distrib]
    refine sum_eq_zero fun t ht ↦ ?_
    have ht := mem_range.1 ht
    obtain ⟨m, hm⟩ : ∃ m, C.serreDeg i j = t + 1 + m := ⟨C.serreDeg i j - (t + 1), by omega⟩
    rw [Nat.add_sub_cancel, Nat.sub_add_eq, ← add_smul]
    refine (congrArg (· • _) ?_).trans (zero_smul k _)
    simp only [chi_self, chi_of_ne _ _ _ hij, serreCoeff, hm]
    linear_combination serre_coeff_rel (C.qi q i) (C.pii π i) (C.parity j).val t m
  · by_cases hlj : l = j
    · subst l
      simp only [↓reduceIte, hli, zero_add]
      have key : ∀ r ∈ range (C.serreDeg i j + 1),
          C.serreCoeff q π i j r • (C.chi q π j i ^ r • PreF.θ k i ^ (C.serreDeg i j - r + r)) =
            (C.serreCoeff q π i j r * C.chi q π j i ^ r) • PreF.θ k i ^ C.serreDeg i j := by
        intro r hr
        rw [Nat.sub_add_cancel (by have := mem_range.1 hr; omega), smul_smul]
      rw [sum_congr rfl key, ← sum_smul]
      refine (congrArg (· • _) ?_).trans (zero_smul k _)
      rw [(C.chi q π).comm j i, chi_of_ne _ _ _ hij]
      simp only [serreCoeff]
      exact serre_coeff_sum (C.qi q i) (C.pii_sq π hπ i) _ hN1 (C.odd_serreDeg_or π hij)
    · simp [hli, hlj]

/-- The left side of each quantum Serre relation (10.1) lies in the radical of the form, for any
normalization `(θᵢ, θᵢ) = nmᵢ` ([CHW1] Prop. 1.7.3), given `π² = 1`. -/
theorem serreElt_mem_radical (hπ : π ^ 2 = 1) (nm : I → k) {i j : I} (hij : i ≠ j) :
    C.serreElt q π i j ∈ PreF.radical (C.chi q π) nm :=
  PreF.mem_radical_of_rDeriv_mem _ _ (C.counit_serreElt q π i j) fun l ↦ by
    rw [C.rDeriv_serreElt q π hπ hij l]; exact zero_mem _

/-- The surjection from [BE2]'s `f` (generators and the relations (10.1)) onto [CHW1]'s
`f = 'f / I`, `θᵢ ↦ θᵢ`. -/
def serreToRadical (hπ : π ^ 2 = 1) : C.serreF q π →ₐ[k] C.radicalF q π :=
  RingQuot.liftAlgHom k ⟨PreF.toQuotient _ _, fun x y h ↦ by
    cases h with
    | serre i j hij =>
      rw [map_zero, PreF.toQuotient_eq_zero_iff]
      exact C.serreElt_mem_radical q π hπ _ hij⟩

theorem serreToRadical_toSerreF (hπ : π ^ 2 = 1) (x : PreF k I) :
    C.serreToRadical q π hπ (C.toSerreF q π x) = PreF.toQuotient _ _ x :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

theorem serreToRadical_surjective (hπ : π ^ 2 = 1) :
    Function.Surjective (C.serreToRadical q π hπ) := fun y ↦ by
  obtain ⟨x, rfl⟩ := PreF.toQuotient_surjective _ _ y
  exact ⟨C.toSerreF q π x, C.serreToRadical_toSerreF q π hπ x⟩

end SuperCartanDatum

end OddMath.CoveringQuantum
