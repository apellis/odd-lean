/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedVacuum.InverseCapMoments
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Algebra.Basic

/-! # Column moments of a positive-height inverse

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8 (the bubble identity `bubbles_eq` of the swapped vacuum recovery).
At positive height `H` the augmented matrix `[s; v; v x; …; v x^(H-1)]` is
inverted by a row `[j, a_0, …, a_(H-1)]`. Its extreme column `a = a_(H-1)`
satisfies `a ≫ s = 0` and `a ≫ x^j ≫ v = δ_(j,H-1)` for `j < H`; its
higher column moments `a ≫ x^(H-1+l) ≫ v` are the normalized left bubbles
(`docs/Nondegeneracy/SwappedVacuumBubbles.md`, §§2–4).

This file proves, from the literal mate slide, the monic probe relation and
the single-cap reservoir window, that the probe-weighted column moments and
the reservoir right moments `u ≫ y^(N-1+l) ≫ ell` are mutually inverse
power series after the sign twist `q^l`
(`inverse_column_reservoir_series`). No bubble value, factor action or
generating-series formula is assumed. The scalar `q` covers both the even
slide (`q = 1`) and the signed odd slide (`q = -1`); unlike the height-zero
cap, no support condition on the probe coefficients is needed, because the
`q^n` term of the slide is killed by `a ≫ s = 0`. See
`docs/Nondegeneracy/InverseColumnMoments.md`.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedVacuum

open CategoryTheory Finset

universe u v w

section Ring

variable {k : Type w} [CommRing k]

theorem pow_add_two_mul_of_mul_self (q : k) (hq : q * q = 1) (a m : ℕ) :
    q ^ (a + 2 * m) = q ^ a := by
  rw [pow_add, pow_mul, sq, hq, one_pow, mul_one]

/-- The probe-weighted column moments: the coefficients of the product of the
reversed probe polynomial with the column moment series `l ↦ b (H-1+l)`. -/
def weightedColumn {R : Type*} [Ring R] [Algebra k R] (c : ℕ → k) (P N : ℕ)
    (b : ℕ → R) (l : ℕ) : R :=
  ∑ n ∈ range (P + 1), if N + 1 ≤ n + l then c n • b (n + l - (N + 1)) else 0

/-- Ring form of the inverse-series identity. `b` are column moments, `t`
reservoir moments; `hrel` is the probe relation composed with the reservoir
cap and `hhigh` the probe relation composed with the column. -/
theorem reservoir_mul_weightedColumn {R : Type*} [Ring R] [Algebra k R]
    (q : k) (hq : q * q = 1) (H N : ℕ) (hH : 0 < H) (hN : 0 < N)
    (c : ℕ → k) (hc : c (H + N) = 1) (b t : ℕ → R)
    (hb : ∀ j < H, b j = if j + 1 = H then 1 else 0)
    (ht : ∀ i < N, t i = if i + 1 = N then 1 else 0)
    (hrel : ∀ d, ∑ n ∈ range (H + N + 1),
      c n • ∑ j ∈ range n, q ^ (n - j) • (t (d + (n - 1 - j)) * b j) = 0)
    (hhigh : ∀ m, ∑ n ∈ range (H + N + 1), c n • b (n + m) = 0) (L : ℕ) :
    ∑ l ∈ range (L + 1), t (N - 1 + (L - l)) * (q ^ l • weightedColumn c (H + N) N b l) =
      if L = 0 then 1 else 0 := by
  rcases L with _ | d
  · rw [sum_range_one, ite_eq_left rfl, Nat.sub_self, add_zero, pow_zero, one_smul,
      ht (N - 1) (by omega), ite_eq_left (by omega), one_mul, weightedColumn, sum_range_succ,
      sum_eq_zero, zero_add, ite_eq_left (by omega), show H + N + 0 - (N + 1) = H - 1 by omega,
      hb _ (by omega), ite_eq_left (by omega), hc, one_smul]
    intro n hn
    rw [mem_range] at hn
    split_ifs with h
    · rw [hb _ (by omega), ite_eq_right (by omega), smul_zero]
    · rfl
  · rw [ite_eq_right (Nat.succ_ne_zero d)]
    set F : ℕ → ℕ → R := fun n l =>
      if l ≤ N ∧ N + 1 ≤ n + l then
        c n • q ^ l • (t (N - 1 + (d + 1 - l)) * b (n + l - (N + 1))) else 0 with hF
    have hsplit : ∀ l ∈ range (d + 1 + 1),
        t (N - 1 + (d + 1 - l)) * (q ^ l • weightedColumn c (H + N) N b l) =
          ∑ n ∈ range (H + N + 1), F n l := by
      intro l _
      by_cases hl : l ≤ N
      · rw [weightedColumn, smul_sum, mul_sum]
        apply sum_congr rfl
        intro n _
        rw [hF]
        dsimp only
        by_cases hnl : N + 1 ≤ n + l
        · rw [ite_eq_left hnl, ite_eq_left ⟨hl, hnl⟩, mul_smul_comm, mul_smul_comm, smul_comm]
        · rw [ite_eq_right hnl, ite_eq_right (fun h => hnl h.2), smul_zero, mul_zero]
      · have hw : weightedColumn c (H + N) N b l = 0 := by
          rw [weightedColumn, ← hhigh (l - (N + 1))]
          apply sum_congr rfl
          intro n _
          rw [ite_eq_left (by omega), show n + l - (N + 1) = n + (l - (N + 1)) by omega]
        rw [hw, smul_zero, mul_zero]
        symm
        apply sum_eq_zero
        intro n _
        rw [hF]
        dsimp only
        rw [ite_eq_right (fun h => hl h.1)]
    rw [sum_congr rfl hsplit, sum_comm, ← smul_zero (q ^ (N + 1)), ← hrel d, smul_sum]
    apply sum_congr rfl
    intro n hn
    rw [mem_range] at hn
    rw [smul_sum, smul_sum]
    have hterm : ∀ j, j < n → n ≤ j + N + 1 → j + N ≤ d + n →
        q ^ (N + 1) • c n • q ^ (n - j) • (t (d + (n - 1 - j)) * b j) =
          F n (j + N + 1 - n) := by
      intro j hj hnj hjd
      rw [hF]
      dsimp only
      rw [ite_eq_left ⟨by omega, by omega⟩, show n + (j + N + 1 - n) - (N + 1) = j by omega,
        show N - 1 + (d + 1 - (j + N + 1 - n)) = d + (n - 1 - j) by omega,
]
      simp only [smul_smul]
      congr 1
      rw [mul_left_comm, ← pow_add,
        show N + 1 + (n - j) = (j + N + 1 - n) + 2 * (n - j) by omega,
        pow_add_two_mul_of_mul_self q hq]
    have hbz : ∀ j, j + 1 < H → b j = 0 := fun j hj => by
      rw [hb j (by omega), ite_eq_right (by omega)]
    have htz : ∀ i, i + 1 < N → t i = 0 := fun i hi => by
      rw [ht i (by omega), ite_eq_right (by omega)]
    symm
    apply sum_bij_ne_zero (fun j _ _ => j + N + 1 - n)
    · intro j hj hne
      rw [mem_range] at hj ⊢
      have h1 : ¬ j + 1 < H := fun h => hne (by rw [hbz j h]; simp)
      have h2 : ¬ d + (n - 1 - j) + 1 < N := fun h => hne (by rw [htz _ h]; simp)
      omega
    · intro j₁ hj₁ hne₁ j₂ hj₂ hne₂ heq
      rw [mem_range] at hj₁ hj₂
      have h1 : ¬ j₁ + 1 < H := fun h => hne₁ (by rw [hbz j₁ h]; simp)
      have h2 : ¬ j₂ + 1 < H := fun h => hne₂ (by rw [hbz j₂ h]; simp)
      omega
    · intro l hl hne
      rw [mem_range] at hl
      have hc' : l ≤ N ∧ N + 1 ≤ n + l := by
        by_contra hcon
        apply hne
        rw [hF]
        dsimp only
        rw [ite_eq_right hcon]
      refine ⟨n + l - (N + 1), mem_range.mpr (by omega), ?_, by omega⟩
      rw [hterm _ (by omega) (by omega) (by omega), show n + l - (N + 1) + N + 1 - n = l by omega]
      exact hne
    · intro j hj hne
      rw [mem_range] at hj
      have h1 : ¬ j + 1 < H := fun h => hne (by rw [hbz j h]; simp)
      have h2 : ¬ d + (n - 1 - j) + 1 < N := fun h => hne (by rw [htz _ h]; simp)
      exact hterm j hj (by omega) (by omega)

end Ring

section Category

variable {k : Type w} [CommRing k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] {V X Y : C}

/-- Expansion of a probe polynomial between two morphisms. -/
theorem comp_capPolynomial_comp {W Z : C} (c : ℕ → k) (P : ℕ) (x : End X)
    (f : W ⟶ X) (g : X ⟶ Z) :
    f ≫ capPolynomial c P x ≫ g = ∑ n ∈ range (P + 1), c n • (f ≫ (x ^ n) ≫ g) := by
  rw [capPolynomial, Preadditive.sum_comp, Preadditive.comp_sum]
  apply sum_congr rfl
  intro n _
  rw [Linear.smul_comp, Linear.comp_smul]

/-- Column moments of the mate slide. For a column `a` killed by `s`, every
`a ≫ x^n ≫ s` followed by a reservoir moment is a combination of column
moments `a ≫ x^j ≫ v` (`j < n`) composed with reservoir moments. -/
theorem column_slide (q : k) (hq : q * q = 1) (x : End X) (y : End Y)
    (s : X ⟶ Y) (u : V ⟶ Y) (v : X ⟶ V) (ell : Y ⟶ V) (a : V ⟶ X)
    (hslide : s ≫ y - q • (x ≫ s) = v ≫ u) (has : a ≫ s = 0) (n : ℕ) :
    ∀ d : ℕ, a ≫ (x ^ n) ≫ s ≫ (y ^ d) ≫ ell =
      -∑ j ∈ range n, q ^ (n - j) •
        ((a ≫ (x ^ j) ≫ v) ≫ u ≫ (y ^ (d + (n - 1 - j))) ≫ ell) := by
  have hxs : x ≫ s = q • (s ≫ y) - q • (v ≫ u) := by
    have h := congrArg (fun f => q • f) hslide
    simp only [smul_sub, smul_smul, hq, one_smul] at h
    rw [← h, sub_sub_cancel]
  induction n with
  | zero =>
    intro d
    rw [pow_zero, End.one_def, Category.id_comp, ← Category.assoc, has, Limits.zero_comp,
      sum_range_zero, neg_zero]
  | succ n ih =>
    intro d
    have hstep : a ≫ (x ^ (n + 1)) ≫ s ≫ (y ^ d) ≫ ell =
        q • (a ≫ (x ^ n) ≫ s ≫ (y ^ (d + 1)) ≫ ell) -
          q • ((a ≫ (x ^ n) ≫ v) ≫ u ≫ (y ^ d) ≫ ell) := by
      rw [pow_succ' x n, End.mul_def, Category.assoc, ← Category.assoc x s, hxs,
        pow_succ y d, End.mul_def]
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp,
        Linear.comp_smul, Category.assoc]
    rw [hstep, ih (d + 1), sum_range_succ, smul_neg, smul_sum, neg_add, sub_eq_add_neg]
    congr 1
    · congr 1
      apply sum_congr rfl
      intro j hj
      rw [mem_range] at hj
      rw [smul_smul, ← pow_succ', show n - j + 1 = n + 1 - j by omega,
        show d + 1 + (n - 1 - j) = d + (n + 1 - 1 - j) by omega]
    · rw [Nat.add_sub_cancel_left, pow_one, show d + (n + 1 - 1 - n) = d by omega]

/-- The probe relation composed with the reservoir cap: the relation `hrel` of
`reservoir_mul_weightedColumn` for the column and reservoir moments (in
`End V` the product `t * b` is the composite `b ≫ t`). -/
theorem column_reservoir_relation (q : k) (hq : q * q = 1) (x : End X) (y : End Y)
    (s : X ⟶ Y) (u : V ⟶ Y) (v : X ⟶ V) (ell : Y ⟶ V) (a : V ⟶ X) (P : ℕ) (c : ℕ → k)
    (hslide : s ≫ y - q • (x ≫ s) = v ≫ u) (has : a ≫ s = 0)
    (hprobe : capPolynomial c P x = 0) (d : ℕ) :
    ∑ n ∈ range (P + 1), c n • ∑ j ∈ range n, q ^ (n - j) •
      ((a ≫ (x ^ j) ≫ v) ≫ u ≫ (y ^ (d + (n - 1 - j))) ≫ ell) = 0 := by
  have h0 : a ≫ capPolynomial c P x ≫ s ≫ (y ^ d) ≫ ell = 0 := by
    rw [hprobe, Limits.zero_comp, Limits.comp_zero]
  rw [comp_capPolynomial_comp, ← neg_eq_zero, ← sum_neg_distrib] at h0
  rw [← h0]
  apply sum_congr rfl
  intro n _
  rw [column_slide q hq x y s u v ell a hslide has n d, smul_neg, neg_neg]

/-- The probe relation composed with the column: the relation `hhigh` of
`reservoir_mul_weightedColumn` for the column moments. -/
theorem column_probe_relation (x : End X) (v : X ⟶ V) (a : V ⟶ X) (P : ℕ) (c : ℕ → k)
    (hprobe : capPolynomial c P x = 0) (m : ℕ) :
    ∑ n ∈ range (P + 1), c n • (a ≫ (x ^ (n + m)) ≫ v) = 0 := by
  have h0 : a ≫ capPolynomial c P x ≫ (x ^ m) ≫ v = 0 := by
    rw [hprobe, Limits.zero_comp, Limits.comp_zero]
  rw [comp_capPolynomial_comp] at h0
  rw [← h0]
  apply sum_congr rfl
  intro n _
  rw [show x ^ (n + m) = (x ^ n) ≫ (x ^ m) by rw [add_comm, pow_add, End.mul_def],
    Category.assoc]

end Category

end OddMath.QuiverHecke.SwappedVacuum
