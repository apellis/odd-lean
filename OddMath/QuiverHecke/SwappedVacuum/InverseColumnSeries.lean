/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedVacuum.InverseColumnMoments
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.Expand

/-! # Power-series form of the positive-height column identity

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8. `inverse_column_reservoir_series` states that the reservoir right
moments and the `q`-twisted probe-weighted column moments are inverse. Here
the probe weighting is factored as a product with the reversed probe
polynomial `ĉ_r = c_(H+N-r)`, giving the identity of power series

  `T(z) · ĉ(z) · B(qz) = 1`,  `T_l = u ≫ y^(N-1+l) ≫ ell`,
  `B_m = a ≫ x^(H-1+m) ≫ v`,

when `ĉ` is invariant under `z ↦ qz` (automatic for `q = 1`, and for the
odd probe `(x² + 1)^M` with `q = -1`). See
`docs/Nondegeneracy/InverseColumnMoments.md`.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedVacuum

open CategoryTheory Finset

universe u v w

variable {k : Type w} [CommRing k]

/-- The probe-weighted column moments are the convolution of the reversed
probe coefficients with the column moments from `H - 1` on. -/
theorem weightedColumn_eq_sum {R : Type*} [Ring R] [Algebra k R] (c : ℕ → k)
    (H N : ℕ) (hH : 0 < H) (b : ℕ → R) (hb0 : ∀ j, j + 1 < H → b j = 0) (l : ℕ) :
    weightedColumn c (H + N) N b l = ∑ r ∈ range (l + 1),
      if r ≤ H + N then c (H + N - r) • b (H - 1 + (l - r)) else 0 := by
  rw [weightedColumn]
  apply sum_bij_ne_zero (fun n _ _ => H + N - n)
  · intro n hn hne
    rw [mem_range] at hn ⊢
    by_cases h : N + 1 ≤ n + l
    · rw [ite_eq_left h] at hne
      have : ¬ n + l - (N + 1) + 1 < H := fun h' => hne (by rw [hb0 _ h', smul_zero])
      omega
    · exact absurd (ite_eq_right h) hne
  · intro n₁ hn₁ _ n₂ hn₂ _ heq
    rw [mem_range] at hn₁ hn₂
    omega
  · intro r hr hne
    rw [mem_range] at hr
    by_cases h : r ≤ H + N
    · refine ⟨H + N - r, mem_range.mpr (by omega), ?_, by omega⟩
      rw [ite_eq_left (show N + 1 ≤ H + N - r + l by omega),
        show H + N - r + l - (N + 1) = H - 1 + (l - r) by omega]
      rw [ite_eq_left h] at hne
      exact hne
    · exact absurd (ite_eq_right h) hne
  · intro n hn hne
    rw [mem_range] at hn
    by_cases h : N + 1 ≤ n + l
    · rw [ite_eq_left h, ite_eq_left (show H + N - n ≤ H + N by omega),
        show H + N - (H + N - n) = n by omega]
      rw [ite_eq_left h] at hne
      have : ¬ n + l - (N + 1) + 1 < H := fun h' => hne (by rw [hb0 _ h', smul_zero])
      rw [show H - 1 + (l - (H + N - n)) = n + l - (N + 1) by omega]
    · exact absurd (ite_eq_right h) hne

/-- Series form of `reservoir_mul_weightedColumn`. -/
theorem reservoirSeries_mul_probe_mul_column {R : Type*} [Ring R] [Algebra k R]
    (q : k) (hq : q * q = 1) (H N : ℕ) (hH : 0 < H) (hN : 0 < N)
    (c : ℕ → k) (hc : c (H + N) = 1) (b t : ℕ → R)
    (hsupp : ∀ r ≤ H + N, q ^ r * c (H + N - r) = c (H + N - r))
    (hb : ∀ j < H, b j = if j + 1 = H then 1 else 0)
    (ht : ∀ i < N, t i = if i + 1 = N then 1 else 0)
    (hrel : ∀ d, ∑ n ∈ range (H + N + 1),
      c n • ∑ j ∈ range n, q ^ (n - j) • (t (d + (n - 1 - j)) * b j) = 0)
    (hhigh : ∀ m, ∑ n ∈ range (H + N + 1), c n • b (n + m) = 0) :
    PowerSeries.mk (fun l => t (N - 1 + l)) *
      (PowerSeries.mk (fun r => if r ≤ H + N then algebraMap k R (c (H + N - r)) else 0) *
        PowerSeries.mk (fun m => q ^ m • b (H - 1 + m))) = 1 := by
  have hb0 : ∀ j, j + 1 < H → b j = 0 := fun j hj => by
    rw [hb j (by omega), ite_eq_right (by omega)]
  have hG : ∀ l, PowerSeries.coeff l
      (PowerSeries.mk (fun r => if r ≤ H + N then algebraMap k R (c (H + N - r)) else 0) *
        PowerSeries.mk (fun m => q ^ m • b (H - 1 + m))) =
        q ^ l • weightedColumn c (H + N) N b l := by
    intro l
    rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      weightedColumn_eq_sum c H N hH b hb0, smul_sum]
    apply sum_congr rfl
    intro r hr
    rw [mem_range] at hr
    simp only [PowerSeries.coeff_mk]
    split_ifs with h
    · rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul, smul_smul]
      congr 1
      calc c (H + N - r) * q ^ (l - r) = q ^ r * c (H + N - r) * q ^ (l - r) := by
            rw [hsupp r h]
        _ = q ^ (r + (l - r)) * c (H + N - r) := by ring
        _ = q ^ l * c (H + N - r) := by rw [show r + (l - r) = l by omega]
    · rw [zero_mul, smul_zero]
  ext L
  rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_one]
  have h := reservoir_mul_weightedColumn q hq H N hH hN c hc b t hb ht hrel hhigh L
  rw [← sum_range_reflect] at h
  rw [← h]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [PowerSeries.coeff_mk, hG, show L + 1 - 1 - i = L - i by omega,
    show L - (L - i) = i by omega]

/-- The odd probe `(x² + 1)^M` has only even coefficients, so its reversed
coefficients satisfy the `q = -1` support hypothesis of
`reservoirSeries_mul_probe_mul_column`. -/
theorem square_add_one_reversed_support (M r : ℕ) (hr : r ≤ 2 * M) :
    (-1 : k) ^ r * ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ M).coeff (2 * M - r) =
      ((Polynomial.X ^ 2 + 1 : Polynomial k) ^ M).coeff (2 * M - r) := by
  rcases Nat.even_or_odd r with he | ho
  · rw [he.neg_one_pow, one_mul]
  · have he : (Polynomial.X ^ 2 + 1 : Polynomial k) ^ M =
        Polynomial.expand k 2 ((Polynomial.X + 1) ^ M) := by
      simp only [map_pow, map_add, Polynomial.expand_X, map_one]
    have hnd : ¬ 2 ∣ 2 * M - r := by
      obtain ⟨m, hm⟩ := ho
      omega
    rw [he, Polynomial.coeff_expand (by decide), ite_eq_right hnd, mul_zero]

end OddMath.QuiverHecke.SwappedVacuum
